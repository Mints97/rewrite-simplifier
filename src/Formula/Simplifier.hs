{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}

module Formula.Simplifier ( ReplacementRule (..), mainSimplifyRule               -- the replacement rule(s) and the default one being used
                          , chcSimplifyRule, shortenNeq
                          , parseExprToExprDAG, convertExprDAGToExpr             -- Expr to ExprDAG, ExprDAG to Expr
                          , matchPatternToDAG, matchExprToDAG                    -- Match in ExprDAG and in Expr
                          , replaceInExprDAG, replaceInExpr, replaceNodeWithExpr -- Replace in ExprDAG and in Expr
                          , simplifyExpr                                         -- simplify
                          , graphToGraphviz
                          )
where

import           Formula (pexpr)
import           Formula.Expr
import           Formula.Var
import           Formula.Type
import           Data.List
import qualified Data.Map as Map
import           Data.Map ((!))
import           Data.Maybe
import           Control.Lens (makeLenses, (&), (.~))
import qualified Data.Set as Set
import           Data.Set (Set)
import           Data.Foldable
import           Control.Monad
import           Control.Arrow (first, second)
import           Control.Applicative ((<$>))
--import Data.Text.Prettyprint.Doc
--import Debug.Trace


-- The children of one node
data NodeChHolder a = NNodeCh [a] -- For "normal" operators
                    | ACNodeCh [a] [a] -- For operators that can be re-ordered and parenthesized arbitrarily. The second list is a sorted version of the first
                    | NCNodeCh -- Empty, no children
                    deriving (Show)

validACNodeCh :: Ord a => [a] -> NodeChHolder a
validACNodeCh xs = ACNodeCh xs (sort xs)

instance Foldable NodeChHolder where
  foldr f b (NNodeCh xs) = foldr f b xs
  foldr f b (ACNodeCh xs _) = foldr f b xs
  foldr _ b NCNodeCh = b

instance Functor NodeChHolder where
  fmap f (NNodeCh xs) = NNodeCh $ map f xs
  fmap f (ACNodeCh xs _) = ACNodeCh (map f xs) (map f xs) -- this doesn't preserve correctness, but we can't constrain a Functor
  fmap _ NCNodeCh = NCNodeCh

instance Ord a => Eq (NodeChHolder a) where
  (NNodeCh is)    == (NNodeCh js)    = is == js
  (ACNodeCh _ is) == (ACNodeCh _ js) = is == js
  NCNodeCh        == NCNodeCh        = True
  _               == _               = False

nodeChToList :: NodeChHolder a -> [a]
nodeChToList (NNodeCh xs) = xs
nodeChToList (ACNodeCh xs _) = xs
nodeChToList NCNodeCh = []

-- Utility. Replaces all matching elements in a list with another value
replace :: Eq a => a -> a -> [a] -> [a]
replace vold vnew = map (\x -> if x == vold then vnew else x)

-- Replaces all matching elements in a node's child list with another value
replaceInCh :: (Eq a, Ord a) => NodeChHolder a -> a -> a -> NodeChHolder a
replaceInCh (NNodeCh is) i ni = NNodeCh $ replace i ni is
replaceInCh (ACNodeCh is _) i ni = ACNodeCh (replace i ni is) (sort $ replace i ni is)
replaceInCh NCNodeCh _ _ = NCNodeCh


-- One node 
data ExprDAGNode = ExprDAGNode
    { _nodeParents   :: Set Int
    , _nodeOperator  :: Expr -- you can theoretically put in an @: - constructed Expr here, but please don't, please
    , _nodeMergeable :: Bool -- this is here as a precaution. This is currently only for the "master node", see below
    , _nodeChildren  :: NodeChHolder Int
    } deriving (Eq, Show)

makeLenses ''ExprDAGNode

-- An empty ExprDAGNode
emptyExprDAGNode :: ExprDAGNode
emptyExprDAGNode = ExprDAGNode Set.empty LUnit True NCNodeCh


-- Represents an expression as a DAG.
-- It is always kept at a state where any equal expressions are merged regardless of position.
-- This will be later made a monad and possibly exposed from the module.
data ExprDAG = ExprDAG
    { _nodesMap   :: Map.Map Int ExprDAGNode
    , _maxIndex   :: Int -- we can't use size since there's no guarantee indices are contiguous
    , _rootIndex  :: Int
    , _addedNodeIndices :: [Int] -- optimization: we can clean this up at any point in time and then track
                                 -- all node indices added after that point.
    } deriving (Show)

makeLenses ''ExprDAG

-- For debug. Produces a string which can be copy-pasted into a .dot file which
-- can be displayed normally in a GraphViz viewer such as XDot.
graphToGraphviz :: ExprDAG -> String
graphToGraphviz g = "digraph G {" ++ foldr (\i acc -> acc ++ graphNodeToGraphviz i) "" (Map.keys (_nodesMap g)) ++ "}"
    where graphNodeToGraphviz i = let node = nodeAt g i
                                   in show i ++ " [label=" ++ ['"'] ++ show i ++ ": " ++ map (\c -> if c == '"' then '`' else c) (show (_nodeOperator node)) ++ ['"'] ++ "]; "
                                             ++ foldr (\ich acc -> acc ++ show i ++ " -> " ++ show ich ++ "; ") "" (_nodeChildren node)

-- An empty ExprDAG. Utility, useful for folds
emptyExprDAG :: ExprDAG
emptyExprDAG = ExprDAG Map.empty (-1) 0 []

-- Gets the node at the ExprDAG at index i
nodeAt :: ExprDAG -> Int -> ExprDAGNode
nodeAt g i = _nodesMap g ! i


-- Indicates whether a match pattern matched to some ExprDAG.
-- A match pattern can contain wildcard variables. This also
-- maps their names to corresponding expression node indices in the ExprDAG
data MatchHolder a = MatchHolder { _matched     :: Bool
                                 , _matchedAt   :: Int
                                 , _matchedVals :: Map.Map Var a
                                 } deriving (Show) -- this may be extended later

instance Eq (MatchHolder a) where
  m1 == m2      = _matchedAt m1 == _matchedAt m2

instance Ord (MatchHolder a) where
  compare m1 m2 = compare (_matchedAt m1) (_matchedAt m2)


makeLenses ''MatchHolder

-- The empty match holder has no entries and is not matched, the starting match
-- holder has no entries but is considered matched. They are utility for folds.
emptyMatchHolder, startingMatchHolder :: MatchHolder a
emptyMatchHolder    = MatchHolder False (-1) Map.empty
startingMatchHolder = emptyMatchHolder & matched .~ True



-- Defines a replacement pattern.
-- Sub-expressions in an ExprDAG which this is applied to are matched to var
-- names in the match pattern, and the names of these vars can be used in the
-- replacement pattern.
-- These data constructors can be used to create complex decision trees for
-- replacing patterns in an ExprDAG. However, in the current default
-- configuration, only about half of them are used.
--
-- SingleReplacement: the basic building block of any ReplacementRule decision
-- tree. Replaces all occurrences of a pattern identified by an ExprDAG
-- with a replacement given as an Expr. The pattern is given as an ExprDAG since
-- it never changes, and it will be eventually need to be converted to an
-- ExprDAG anyway, but it's better to do this earlier, since otherwise it might
-- not get memoized in some cases. And this way you'll just have mkSR calls as
-- parts of thunks, so it will be more efficient. I think. I'm not sure. The
-- replacement pattern is given as an Expr since I'm just piggybacking on the
-- functionality for adding an Expr to a DAG to insert it.
-- Important: a SingleReplacement is applied to all new nodes which get added
-- to the ExprDAG after a single replacement pass, and this is repeated until
-- added nodes can no longer be matched.
--
-- E.g. simplifying (a && b && c) || (a && b && d) for distributivity with a
-- match pattern such as (a && Ra) || (a && Rb), the first round of replacement
-- might yield a && ((b && c) || (b && d)). Here, (b && c) || (b && d) will
-- correspond to one of the newly added nodes, so the pattern will be applied
-- to it as well, and we will end up with a && b (c || d).
-- Applying a SingleReplacement will yield the simplified expression, if
-- replacements have been made, or Nothing if none could be made.
--
-- Replacements are made by matching a pattern to an ExprDAG. Any variable in
-- that pattern acts like a regex capture group: it can be matched to any node
-- (except for special-match variables, these are described below in this
-- paragraph). So, if you have x > y + z, and you match it with a pattern a > b,
-- then, in the resulting MatchHolder, a will be matched to x, and b will be
-- matched to y + z. These variables can and should be used in a replacement
-- Expr in a SingleReplacement, and they will be replaced by whatever they
-- were matched to!
-- There are a few specifics to how these variables are matched:
--
-- If the same variable is present in multiple places in the match pattern, it
-- MUST match the same node for the match to be successful!
--
-- when matching children of an associative and commutative operator such as
-- +, *, || or &&, a regular variable in a match pattern will match exactly
-- one of its children (which can number two or more: regular AST nodes with
-- assoc&comm operators which have children with the same operator are collapsed
-- together into one large node with an unordered list of children).
--
-- When there is an assoc&comm operator, there might be different ways to apply
-- a pattern to it. A match process is recursive, an every step produces a list
-- of all possible matches. However, on each step, all matches where a variable
-- got matched to different nodes are eliminated. So, if you have
-- (x && y) || (x && z), applying pattern (a && Rb) || (b && Rc) will yield
-- 2^3 = 8 possible matches, one with a matched to x, Rb to y, b to x and Rc
-- to z, one with a to x, Rb to y, b to z and R Rc to x, etc. However, if you
-- apply pattern (a && Rb) || (a && Rc), it will force a to be matched to the
-- same node, so there will be only two possible matches: a to x, Rb to y,
-- Rc to z; and a to x, Rb to z, Rc to y. Note that only one of these possible
-- match results is used in the end by anything that calls matchPatternToNode.
-- And since we only take the head of the resulting list, and matchPatternToNode
-- is lazy enough, the rest aren't even computed most of the time (I think).
-- This would have been so hard to implement efficiently in a non-lazy language...
-- 
-- Variables in a match pattern which have their name starting with R
-- (stands for "Rest") have a special meaning: they can be matched to an
-- arbitrary number of an assoc&comm node's children: e.g. if you match
-- x && y && z && n with pattern a && Ra, a might get matched to x, and then Ra
-- will get matched to y && z && n (and when a is matched to y, Ra is x && z && n,
-- etc.) You can have multiple R variables as children of the same accos&comm
-- node. Then the one that comes first in alphabetical order is used, and the
-- rest are used as normal variables (just please don't try that, it's stupid,
-- and I didn't even bother to test that tbh). R variables have no special
-- meaning unless they are children of assoc&comm nodes. If an assoc&comm match
-- pattern node with no R children is matched to an assoc&comm graph node which
-- has more children than it, an implicit variable with the name Rli and type
-- Unit is created, and used as an R variable in the pattern. Here, i is
-- replaced with a number indicating recursion depth, starting from 0. So the Rl
-- node created at the top level of a match pattern will be Rl0. Creating a
-- situation where more than one Rl node is made per depth level can be messy,
-- because they, like any other variable, have to be matched to the exact
-- same thing.
-- This is a limitation: you can't, say, reliably match a && node with exactly 2
-- children. Although I don't really see why you would need to...
-- A cool thing about Rl vars is that if an Rli wasn't matched, and you have it
-- in your replacement pattern as the child of an assoc&comm node, it just won't
-- get added, and the assoc&comm node will have one less child (or, if there's
-- only one other child, it will be added instead). This is done so that you
-- don't have to create multiple ReplacementRule-s, one to replace a && b, and
-- one to replace Ra && a && b (because we are always matching whole nodes, and
-- we never know how many children an assoc&comm node might have). That could
-- actually bog down performance with computationally-intensive match patterns
-- like the ones needed to handle distributivity.
--
-- Variables in a match pattern which have their name starting with N, P or D
-- are only matched to nodes with integer values (LInt). N is matched only to
-- negative integers, P - only to positive, and D matches any integer. For N and
-- P, an additional variable is added to the match holder with a negation of the
-- value. E.g. if you have Na which matched -2, the match holder will have
-- (Na, -2) and (Pa, 2) added to it; and if you have Px which matched 4, the
-- match holder will have (Px, 4) and (Nx, -4) added to it. This is useful for
-- arithmetic carry-over replacement rules.
--
--
--
-- Other ReplacementRule data constructors:
--
-- SequenceReplacement: applies a list of ReplacementRule-s in sequence. This
-- means that a ReplacementRule is applied to what is yielded from the last of
-- the previous ones to be successful.
-- It yields a simplified Expr only if all ReplacementRules in the sequence were
-- successfully applied. Otherwise, it returns Nothing. This can be used for
-- backtracking out of an entire branch of a decision tree.
--
-- LongestSequenceReplacement: applies a list of ReplacementRule-s in sequence.
-- If the very first one can not be successfully applied, it yields Nothing.
-- Otherwise, it keeps applying the ReplacementRule-s from the sequence until
-- the first failure. When that happens, it yields the currently simplified
-- result.
--
-- SpeculativeResult: I don't remember what was the idea behind this one. Erases
-- the result state of some other ReplacementRule: e.g. if the other
-- ReplacementRule, given g, yields Just g', this will yield Just g', and if the
-- other ReplacementRule yields Nothing, this will yield Just g.
--
-- AlternateSingleReplacement: applies a list of ReplacementRule-s to the same
-- ExprDAG (not in sequence). The first one to be successful is used. If none
-- are successful, yields Nothing.
--
-- AnyInSequenceReplacement: applies a list of ReplacementRule-s in sequence.
-- Unsuccessful ones are skipped, and the result of the last successful
-- replacement is used when a subsequent ReplacementRule is applied.
-- ReplacementRules are applied until the list is exhausted. If no
-- ReplacementRule-s in the list are successful, it yields Nothing.
--
-- WhilePossibleReplacement: repeatedly performs an AnyInSequenceReplacement
-- using a list of ReplacementRule-s until the AnyInSequenceReplacement yields
-- Nothing. If the AnyInSequenceReplacement yields Nothing on the first try,
-- this also yields Nothing. Effectively, this applies a sequence of
-- ReplacementRule-s again and again until none of them can be applied anymore.
-- Very inefficient.
data ReplacementRule = SingleReplacement          ExprDAG Expr
                     | SequenceReplacement        [ReplacementRule]
                     | LongestSequenceReplacement [ReplacementRule]
                     | SpeculativeReplacement     ReplacementRule
                     | AlternateSingleReplacement [ReplacementRule]
                     | AnyInSequenceReplacement   [ReplacementRule]
                     | WhilePossibleReplacement   [ReplacementRule]

-- Shorthand for making a SingleReplacement
mkSR :: Expr -> Expr -> ReplacementRule
mkSR e = SingleReplacement (fst $ parseExprToExprDAG e)


-- Replacement rules used:

expandNeq :: ReplacementRule
expandNeq = mkSR [pexpr|a != b|] [pexpr|not (a = b)|]

-- This replacement rule should be run first. It swaps all >= with <=
-- and all > with <. This way you don't have to try matching all 4,
-- since after this, this and the other rules will maintain that <= and < will
-- always be used.
gtToLt :: ReplacementRule
gtToLt = mkSR [pexpr|a > b|] [pexpr|b < a|]

geqToLeq :: ReplacementRule
geqToLeq = mkSR [pexpr|a >= b|] [pexpr|b <= a|]

-- This and similar rules might theoretically come in handy,
-- but I've never seen a situation where we'd really need them.
-- Better to be more efficient and ignore them.
{-
additionCancelOut :: ReplacementRule
additionCancelOut = mkSR [pexpr|a - a|] [pexpr|Rl0 + 0|]
-}

-- This is as simple as getting rid of all subtraction by carrying over to the other
-- side of the comparison operators. Note that all subtraction is represented as
-- addition and multiplying by -1, e.g. a - b becomes a + (-1) * b! If we carry
-- this over, we'll have 1 * b on the rhs, which is why we need the
-- afterCarryOver rule to have the 1 * Ra part.
-- carryOverEq only needs to define 2 cases because = is treated as assoc&comm,
-- even though it is not associative: the only difference is that it is not
-- ever collapsed.
carryOverEq :: ReplacementRule
carryOverEq = AnyInSequenceReplacement [ mkSR [pexpr|Ra + Nx * b = c|] [pexpr|Ra = Px * b + c|]
                                       , mkSR [pexpr|Ra + Nx = c|] [pexpr|Ra = Px + c|]
                                       ]

carryOverLt :: ReplacementRule -- I guess != can be left out, David didn't even include it in the expr parser's grammar...
carryOverLt = AnyInSequenceReplacement [ mkSR [pexpr|c < Ra + Nx * b|] [pexpr|c + Px * b < Ra|]
                                       , mkSR [pexpr|Ra + Nx * b < c|] [pexpr|Ra < c + Px * b|]
                                       , mkSR [pexpr|c < Ra + Nx|] [pexpr|c + Px < Ra|]
                                       , mkSR [pexpr|Ra + Nx < c|] [pexpr|Ra < c + Px|]
                                       ]

carryOverLeq :: ReplacementRule
carryOverLeq = AnyInSequenceReplacement [ mkSR [pexpr|c <= Ra + Nx * b|] [pexpr|c + Px * b <= Ra|]
                                        , mkSR [pexpr|Ra + Nx * b <= c|] [pexpr|Ra <= c + Px * b|]
                                        , mkSR [pexpr|c <= Ra + Nx|] [pexpr|c + Px <= Ra|]
                                        , mkSR [pexpr|Ra + Nx <= c|] [pexpr|Ra <= c + Px|]
                                        ]

afterCarryOver :: ReplacementRule
afterCarryOver = AnyInSequenceReplacement [ mkSR [pexpr|0 + Ra|] [pexpr|Ra|]
                                          , mkSR [pexpr|1 * Ra|] [pexpr|Ra|]
                                          ]


-- A simple identity for <. It produces some not-s which we might eliminate
-- later!
ltToNeq :: ReplacementRule
ltToNeq = mkSR [pexpr|(a < b) || (b < a)|] [pexpr|Rl0 || not (a = b)|]

-- Start getting rid of not-s
doubleNegation :: ReplacementRule
doubleNegation = mkSR [pexpr|not (not a)|] [pexpr|a|]

-- The first rules that do this are those that do not introduce extra complexity
complementOr :: ReplacementRule
complementOr = mkSR [pexpr|a || (not a)|] [pexpr|true|]

complementAnd :: ReplacementRule
complementAnd = mkSR [pexpr|a && (not a)|] [pexpr|false|]

-- After running the complement rules, we can try doing this, and then try them
-- again.
-- This is because sometimes we get stuff like (not a && b) || (a || not b)
-- And a combination of this and the complement rules will eliminate it.
-- However, we only want to keep the results if both the reverse DeMorgans and
-- the complement succeed, so we'll use SequenceReplacement. Otherwise we'd get
-- a ton of bloat.
reverseDeMorgans :: ReplacementRule
reverseDeMorgans = AnyInSequenceReplacement [ mkSR [pexpr|a || not b|] [pexpr|Rl0 || (not (not a && b))|]
                                            , mkSR [pexpr|not a || not b|] [pexpr|Rl0 || (not (a && b))|]
                                            , mkSR [pexpr|a && not b|] [pexpr|Rl0 && (not (not a || b))|]
                                            , mkSR [pexpr|not a && not b|] [pexpr|Rl0 && (not (a || b))|]
                                            ]


-- The rules below only make sense to run right after the "complement" rules above
-- (we don't expect true or false literals to appear in the input by themselves).
-- This and some other cases may warrant a way to chain replacements so that we
-- would limit matching to the parents (as in this case) or children of the
-- previously matched pattern, i.e. the parents of false would get matched for
-- a || false and a && false. This may make the process a bit faster.
annulmentOr, identityOr, annulmentAnd, identityAnd :: ReplacementRule
annulmentOr = mkSR [pexpr|Ra || true|] [pexpr|true|]
identityOr = mkSR [pexpr|Ra || false|] [pexpr|Ra|]
annulmentAnd = mkSR [pexpr|Ra && false|] [pexpr|false|]
identityAnd = mkSR [pexpr|Ra && true|] [pexpr|Ra|]

-- This gives us a few not-s which we might be able to later eliminate with
-- negateLeqLt. Putting this before doubleNegation and complement wouldn't have
-- made a difference.
deMorgansNots :: ReplacementRule
deMorgansNots = AnyInSequenceReplacement [ mkSR [pexpr|not (not a && Rb)|] [pexpr|a || (not Rb)|]
                                         , mkSR [pexpr|not (a && Rb)|] [pexpr|(not a) || (not Rb)|]
                                         , mkSR [pexpr|not (not a || Rb)|] [pexpr|a && (not Rb)|]
                                         , mkSR [pexpr|not (a || b)|] [pexpr|(not a) && (not b)|]
                                         ]

-- Get rid of some of the remaining not-s
negateLeqLt :: ReplacementRule
negateLeqLt = AnyInSequenceReplacement [ mkSR [pexpr|not (a <= b)|] [pexpr|b < a|]
                                       , mkSR [pexpr|not (a < b)|] [pexpr|b <= a|]
                                       ]

deMorgansRest :: ReplacementRule
deMorgansRest = AnyInSequenceReplacement [ mkSR [pexpr|not (not a && not b)|] [pexpr|a || b|]
                                         , mkSR [pexpr|not (not a || not b)|] [pexpr|a && b|]
                                         ]

-- We've rid ourselves of all or most not-s, so we can do the rest with no
-- problem!
idempotenceOr, idempotenceAnd :: ReplacementRule
idempotenceOr = mkSR [pexpr|a || a|] [pexpr|Rl0 || a|]
idempotenceAnd = mkSR [pexpr|a && a|] [pexpr|Rl0 && a|]

-- At this point, we're guaranteed that we won't have and >='s, so we can use
-- this simple identity.
leqToEq :: ReplacementRule
leqToEq = mkSR [pexpr|(a <= b) && (b <= a)|] [pexpr|Rl0 && (a = b)|]

-- I am deciding on whether to move this earlier, since it can ease the job of
-- some of the previous matchers by reducing complexity, but benefits from how
-- they reduce complexity as well. It's a tradeoff.
absorptiveOr, absorptiveAnd :: ReplacementRule
absorptiveOr = mkSR [pexpr|a || (a && Rb)|] [pexpr|Rl0 || a|]
absorptiveAnd = mkSR [pexpr|a && (a || Rb)|] [pexpr|Rl0 && a|]

-- These are really resource-intensive, so they are saved for last, when the
-- expression has been sufficiently reduced by the other rules.
-- They might need to be repeated: imagine (a && b) || (a && c), this would get
distributiveOr, distributiveAnd :: ReplacementRule 
distributiveOr = mkSR [pexpr|(a && Rb) || (a && Rc)|] [pexpr|Rl0 || (a && (Rb || Rc))|]
distributiveAnd = mkSR [pexpr|(a || Rb) && (a || Rc)|] [pexpr|Rl0 && (a || (Rb && Rc))|]

-- no idea if this actually helps Z3 or not, but makes stuff more readable
shortenNeq :: ReplacementRule
shortenNeq = mkSR [pexpr|not (a = b)|] [pexpr|a != b|]

mainSimplifyRule :: ReplacementRule
mainSimplifyRule = AnyInSequenceReplacement [ expandNeq
                                            , carryOverEq
                                            , gtToLt, carryOverLt
                                            , geqToLeq, carryOverLeq
                                            , afterCarryOver
                                            , ltToNeq
                                            , doubleNegation
                                            , complementOr, annulmentOr, identityAnd
                                            , complementAnd, identityOr, annulmentAnd
                                            , SequenceReplacement [ reverseDeMorgans
                                                                  , AnyInSequenceReplacement [ complementOr, annulmentOr, identityAnd
                                                                                             , complementAnd, identityOr, annulmentAnd
                                                                                             ]
                                                                  ]
                                            , WhilePossibleReplacement [ deMorgansNots ]
                                            , complementOr, annulmentOr, identityAnd  -- are these needed here?
                                            , complementAnd, identityOr, annulmentAnd -- ?
                                            , negateLeqLt
                                            , WhilePossibleReplacement [ deMorgansRest ]
                                            , idempotenceOr, idempotenceAnd
                                            , leqToEq, ltToNeq
                                            , absorptiveOr, absorptiveAnd
                                            , distributiveOr --LongestSequenceReplacement [ distributiveOr, distributiveOr ]
                                            , distributiveAnd --LongestSequenceReplacement [ distributiveAnd, distributiveAnd ]
                                            , shortenNeq
                                            , idempotenceOr, idempotenceAnd
                                            ]

chcSimplifyRule :: ReplacementRule
chcSimplifyRule = AnyInSequenceReplacement [ expandNeq, carryOverEq, afterCarryOver ]

-- all possible subsets of an array of size k, and the remainders.
-- Based on https://stackoverflow.com/a/14286085/3079266
choose :: [b] -> Int -> [([b], [b])]
xs     `choose` 0       = [([], xs)]
[]     `choose` _       = []
(x:xs) `choose` k       = let chxs = xs `choose` (k - 1)
                              chxs2 = xs `choose` k
                           in fmap (first ((:) x)) chxs ++ fmap (second ((:) x)) chxs2


-- Adds a Var - index pair to a MatchHolder
addToMatchHolder :: MatchHolder a -> Var -> a -> MatchHolder a
addToMatchHolder mholder v n = (startingMatchHolder & matchedAt .~ _matchedAt mholder) & matchedVals .~ Map.insert v n (_matchedVals mholder)

-- Merges the match values of two MatchHolders.
-- _matchedAt is not checked for equality and the one from the first argument,
-- m1, is used
mergeMatchHolders :: (Eq a) => MatchHolder a -> MatchHolder a -> MatchHolder a
mergeMatchHolders m1 m2 = let matched1 = _matchedVals m1
                              matched2 = _matchedVals m2
                           in if _matched m1 && _matched m2 && isNothing (find (\k -> (matched1 ! k) /= (matched2 ! k)) (Map.keys $ Map.intersection matched1 matched2))
                                then (startingMatchHolder & matchedAt .~ _matchedAt m1) & matchedVals .~ Map.union matched1 matched2
                                else emptyMatchHolder



-- Matches an Expr to a node in the ExprDAG and returns a mapping
-- of vars in the Expr to nodes in the ExprDAG. The process is described in
-- detail in the ReplacementRule description above.
--
-- This is the heart and soul of the entire simplifier, and, as is fitting, it
-- is a true monstrosity! Approach it with caution!
matchPatternToNode :: Int -> Int -> ExprDAG -> Int -> ExprDAG -> [MatchHolder ExprDAGNode]
matchPatternToNode lvl im gm i g = let nodem = nodeAt gm im
                                       res = checkCh (_nodeOperator node) (_nodeOperator nodem)
                                                     (_nodeChildren node) (_nodeChildren nodem)
                                    in map (\mholder -> mholder & matchedAt .~ i) res
                          where node = nodeAt g i
                              
                                checkCh :: Expr -> Expr -> NodeChHolder Int -> NodeChHolder Int -> [MatchHolder ExprDAGNode]
                                checkCh op opm (ACNodeCh nodech _) (ACNodeCh mch _) | op == opm
                                                                        = let listch = toList nodech
                                                                              listmch = toList mch
                                                                           in if length nodech > length mch
                                                                                then matchACNodeCh op listch (partitionMatchPattern listmch) -- =<< allMatchPatternPartitions gm listmch
                                                                                else if length nodech == length mch
                                                                                       then fst =<< matchChAnyOrder listch listmch
                                                                                       else []
                                checkCh op opm (NNodeCh nodech) (NNodeCh mch) | op == opm  =  matchChInOrder nodech mch
                                checkCh (LInt v1) (LInt v2) NCNodeCh NCNodeCh | v1 == v2  = [startingMatchHolder]
                                checkCh (LBool v1) (LBool v2) NCNodeCh NCNodeCh | v1 == v2  = [startingMatchHolder]
                                checkCh LUnit LUnit NCNodeCh NCNodeCh = [startingMatchHolder]
                                checkCh (LInt val) (V v@(Var ('N':name) _)) NCNodeCh NCNodeCh | val < 0  = let n = ExprDAGNode Set.empty (LInt (-val)) True NCNodeCh
                                                                                                            in [addToMatchHolder (addToMatchHolder startingMatchHolder v node)
                                                                                                                                 (v & varName .~ 'P':name)
                                                                                                                                 (n & nodeParents .~ Set.empty)]
                                checkCh (LInt val) (V v@(Var ('P':name) _)) NCNodeCh NCNodeCh | val > 0  = let n = ExprDAGNode Set.empty (LInt (-val)) True NCNodeCh
                                                                                                            in [addToMatchHolder (addToMatchHolder startingMatchHolder v node)
                                                                                                                                 (v & varName .~ 'N':name)
                                                                                                                                 (n & nodeParents .~ Set.empty)]
                                checkCh (LInt _) (V v@(Var ('D':_) _)) NCNodeCh NCNodeCh = [addToMatchHolder startingMatchHolder v (node & nodeParents .~ Set.empty)]
                                checkCh _ (V (Var ('N':_) _)) _ NCNodeCh = [] -- Nx matches only negative integers!
                                checkCh _ (V (Var ('P':_) _)) _ NCNodeCh = [] -- Px matches only positive integers!
                                checkCh _ (V (Var ('D':_) _)) _ NCNodeCh = [] -- Dx matches only integers!
                                checkCh _ (V v) _ NCNodeCh = [addToMatchHolder startingMatchHolder v (node & nodeParents .~ Set.empty)] -- matcher is a var, just put it there
                                checkCh _ _ _ _ = [] -- node type mismatch!

                                splitMatchPattern :: [Int] -> ([Int], [Int])
                                splitMatchPattern = foldr addToPartition ([], [])
                                                where addToPartition ci (l1, l2) = case _nodeOperator $ nodeAt gm ci of
                                                        (V (Var ('R':_) _)) -> (l1, ci:l2)
                                                        _                   -> (ci:l1, l2)

                                partitionMatchPattern :: [Int] -> ([Int], Var)
                                partitionMatchPattern is = let (ns, rs) = splitMatchPattern is
                                                               (ns', V rs') = case rs of
                                                                                []   -> (ns, V $ Var ('R':'l':show lvl) Unit)
                                                                                [ci] -> (ns, _nodeOperator $ nodeAt gm ci)
                                                                                _    -> let sorted = sortOn (_nodeOperator . nodeAt gm) rs               -- sooo... if you're writing a pattern, keep it
                                                                                         in (ns ++ tail sorted, _nodeOperator $ nodeAt gm (head sorted)) -- one R per term. Please.
                                                            in (ns', rs')

                                matchOneVarToSomeCh op v remch mholder = let n = case remch of -- this should only be called for an ACNodeCh
                                                                                     [remchi] -> nodeAt g remchi
                                                                                     _        -> ExprDAGNode Set.empty op True (validACNodeCh remch) -- addOpToDAG gs op remch
                                                                          in mergeMatchHolders mholder (addToMatchHolder startingMatchHolder v n)

                                matchACNodeCh :: Expr -> [Int] -> ([Int], Var) -> [MatchHolder ExprDAGNode]
                                matchACNodeCh op listch (listmch, v@(Var ('R':_) _)) = (\(matches, rest) -> map (matchOneVarToSomeCh op v rest) matches) =<< matchChAnyOrder listch listmch
                                matchACNodeCh _ _ (_, Var _ _) = []

                                matchChAnyOrder :: [Int] -> [Int] -> [([MatchHolder ExprDAGNode], [Int])]
                                matchChAnyOrder listch listmch = let res = map (\((li, lrem), lm) -> (matchChInOrder li lm, lrem))
                                                                               (zip ((\(l, lrem) -> zip (permutations l) (repeat lrem)) =<< (listch `choose` length listmch))
                                                                                    (repeat listmch))
                                                                  in if null res then [([], [])] else res

                                matchChInOrder :: [Int] -> [Int] -> [MatchHolder ExprDAGNode]
                                matchChInOrder listch listmch = foldr (\(ic, imc) prevms -> mixWithNewMatchHolder prevms ic imc)
                                                                      [startingMatchHolder] (zip listch listmch)
                                -- Alternatively: use the Maybe monad for early escape. Doesn't seem to affect performance...
                                -- matchChInOrder listch listmch = fromMaybe [] (foldM (\prevms (ic, imc) -> mixWithNewMatchHolder prevms ic imc <$ guard (not $ null prevms))
                                --                                                     [startingMatchHolder] (zip listch listmch))

                                mixWithNewMatchHolder :: [MatchHolder ExprDAGNode] -> Int -> Int -> [MatchHolder ExprDAGNode]
                                mixWithNewMatchHolder prevmholders ic imc = filter _matched $ prevmholders >>= (\mholder -> map (mergeMatchHolders mholder) (matchPatternToNode (lvl + 1) imc gm ic g))


-- Matches a pattern to a set of indices in an ExprDAG
matchPatternToIndices :: ExprDAG -> ExprDAG -> [Int] -> [MatchHolder ExprDAGNode]
matchPatternToIndices gm g is = filter _matched (map fetchMatch is)
                  where fetchMatch i = let matches = matchPatternToNode 0 (_rootIndex gm) gm i g
                                           match = head matches
                                        in if not (Map.member i (_nodesMap g)) || null matches
                                             then emptyMatchHolder
                                             else match

-- Matches a pattern given by an ExprDAG to an ExprDAG
matchPatternToDAG :: ExprDAG -> ExprDAG -> [MatchHolder ExprDAGNode]
matchPatternToDAG gm g = matchPatternToIndices gm g (Map.keys $ _nodesMap g)

-- Inserts the nodes matched to vars in a list of matcholders into a DAG and
-- updates the list with indices/offsets in the (reversed) list of the indices
-- of newly added nodes. This list will then become the list of children of the
-- master node, which will point to all nodes matched by match variables, even
-- after they are replaced!
insertFauxNodesToDAG :: ExprDAG -> [MatchHolder ExprDAGNode] -> (ExprDAG, ([Int], [MatchHolder Int]))
insertFauxNodesToDAG g = foldr addMatchNodesToDAG (g, ([], [])) -- technically this inserts ALL the matched nodes, not just faux, but all of them get removed later anyway
    where addMatchNodesToDAG (MatchHolder m mat mvals) (gc, (is, ms)) = second (second ((:ms) . MatchHolder m mat . Map.fromList)) (foldr addMatchedNodeToDAG (gc, (is, [])) (Map.toList mvals))
          addMatchedNodeToDAG (v, node) (gc, (is, mvs)) = second (\i -> (i:is, (v, length is):mvs)) (addNodeToDAG gc (_maxIndex gc + 1) node)


-- Matches a pattern to an ExprDAG, then replaces all the matches, and then
-- matches to all the newly added nodes, as described above.
replacePatternInDAG :: ExprDAG -> Expr -> ExprDAG -> Maybe ExprDAG
replacePatternInDAG gm er g = let matches = matchPatternToIndices gm g (Map.keys $ _nodesMap g)
                                  (gc', (nis, matches')) = insertFauxNodesToDAG (emptyAddedNodeIndices g) (sortMatches matches)
                                  (gc'', imaster) = makeMasterNode gc' nis
                               in if isNothing (find _matched matches)
                                    then Nothing
                                    else Just $ removeNodeFromDAG (matchesReplacement matches' imaster gc'') imaster
                      where sortMatches [] = [] -- A MatchHolder which has another MatchHolder's _matchedAt as one of its node's children should be processed earlier
                            sortMatches ms = let (ls, rs) = partition (\m -> isNothing $ find (\m' -> isJust $ find (== _matchedAt m)
                                                                                                                    ((nodeChToList . _nodeChildren) =<< Map.elems (_matchedVals m')))
                                                                                              ms) -- Too many nested lambdas! Like I'm writing JavaScript code...
                                                                      ms
                                              in ls ++ sortMatches rs
                      
                            emptyAddedNodeIndices gc = gc & addedNodeIndices .~ []

                            makeMasterNode gc matchindices = let (gc', i) = addOpToDAG gc (Distinct Unit) matchindices
                                                              in (insertNodeToDAGAt gc' i (nodeAt gc' i & nodeMergeable .~ False), i)

                            makeReplacementPass gc is = let matches = matchPatternToIndices gm gc is
                                                            (gc', (nis, matches')) = insertFauxNodesToDAG (emptyAddedNodeIndices gc) (sortMatches matches)
                                                            (gc'', imaster) = makeMasterNode gc' nis
                                                         in if isNothing (find _matched matches)
                                                              then gc
                                                              else removeNodeFromDAG (matchesReplacement matches' imaster gc'') imaster 

                            matchesReplacement matches imaster gc = let g' = foldr (\match gc' -> if not (Map.member (_matchedAt match) (_nodesMap gc'))
                                                                                                    then gc'
                                                                                                    else fst $ replaceNodeWithExpr match imaster gc' er)
                                                                           (emptyAddedNodeIndices gc) (reverse matches)
                                                             in makeReplacementPass g' (_addedNodeIndices g')
                                   

-- Matches a pattern given by an Expr to an ExprDAG by first converting the
-- pattern to an ExprDAG and then matching it.
matchExprToDAG :: Expr -> ExprDAG -> [MatchHolder ExprDAGNode]
matchExprToDAG e = matchPatternToDAG (fst $ parseExprToExprDAG e)




-- Inserts one node to a DAG at a specified index
insertNodeToDAGAt :: ExprDAG -> Int -> ExprDAGNode -> ExprDAG
insertNodeToDAGAt g i node = let newmap = Map.insert i node (_nodesMap g)
                                 newmax = if i > _maxIndex g then i else _maxIndex g
                              in (g & nodesMap .~ newmap) & maxIndex .~ newmax


-- Removes a node at a given index from a DAG
-- DOES NOT remove it as its parents' child!
-- This makes it possible to use this to insert something else in its place
removeNodeFromDAG :: ExprDAG -> Int -> ExprDAG
removeNodeFromDAG g i = let node = nodeAt g i
                            g' = g & nodesMap .~ Map.delete i (_nodesMap g)
                         in foldr (\ich gc -> if not $ Map.member ich (_nodesMap gc)
                                                then gc 
                                                else let cnode = nodeAt gc ich -- remove node as parent of its children
                                                         nodep = _nodeParents cnode
                                                      in if Set.size nodep == 1 && _rootIndex gc /= ich && Set.member i nodep -- the rhs of && is kind of a hack:
                                                           then removeNodeFromDAG gc ich              --   if a node has two links to a child, we'll see that child twice!
                                                           else insertNodeToDAGAt gc ich (cnode & nodeParents .~ Set.delete i nodep))
                                  g' (_nodeChildren node)


-- Adds a set of indices to a node's parents set. The parameters are in such an
-- order because I used this for a foldr in a few places. I need to figure out a
-- reasonable parameter order for the other functions...
updateNodeParents :: Set Int -> Int -> ExprDAG -> ExprDAG
updateNodeParents iparents i g = let node = nodeAt g i
                                  in insertNodeToDAGAt g i (node & nodeParents .~ Set.union iparents (_nodeParents node))


-- Assumes that any child nodes with the same op have already been collapsed
-- Don't call this on normal nodes!
--
-- This works because all assoc-comm children of an assoc-comm node will already
-- have been collapsed by the time we parse it because we parse children first,
-- operator second.
collapseCommAssoc :: ExprDAG -> Expr -> [Int] -> ([Int], Maybe Int)
collapseCommAssoc g op ich = let ichUpdated = ich >>= (\i -> if _nodeOperator (nodeAt g i) == op then getACCh $ _nodeChildren $ nodeAt g i else [i])
                                 collapseToM = find (\i -> _nodeOperator (nodeAt g i) == op && Set.size (_nodeParents $ nodeAt g i) == 0) ich -- if there's a parentless child, it's the target
                              in case op of
                                  Eql _ -> (ich, Nothing)
                                  _     -> (ichUpdated, collapseToM)
                           where getACCh (ACNodeCh ch _) = reverse ch
                                 getACCh _ = []


-- Find an equivalent node, which should have the same operator and child
-- incides as the given node.
--
-- This works for merging equivalent nodes because we parse children before
-- parents, so, if a node equivalent to this one has been or will be found, its
-- children will have been parsed before it, and, if they are all equivalent to
-- this node's children, they will have the same indices.
findEquivalentNodeInDAG :: ExprDAG  -> ExprDAGNode -> Maybe Int
findEquivalentNodeInDAG g node = let findNodeID = find (\(_, tnode) -> _nodeMergeable tnode && checkOneNode (_nodeOperator node) (_nodeOperator tnode)
                                                                                                            (_nodeChildren node) (_nodeChildren tnode))
                                                       (Map.toList $ _nodesMap g)
                                  in if _nodeMergeable node then fst <$> findNodeID else Nothing
                            where checkOneNode :: Expr -> Expr -> NodeChHolder Int -> NodeChHolder Int -> Bool
                                  checkOneNode nodeop op (ACNodeCh _ nodech) (ACNodeCh _ ch) = nodeop == op && nodech == ch
                                  checkOneNode nodeop op (NNodeCh nodech) (NNodeCh ch) = nodeop == op && nodech == ch
                                  checkOneNode nodeop op NCNodeCh NCNodeCh = nodeop == op -- actually a leaf
                                  checkOneNode _ _ _ _ = False -- node type mismatch!


-- Adds an already-constructed ExprDAGNode to an ExprDAG at some index. If it
-- already exists at another index, it is not added.
addNodeToDAG :: ExprDAG -> Int -> ExprDAGNode -> (ExprDAG, Int)
addNodeToDAG g ires node = let g' = insertNodeToDAGAt g ires node
                               g'' = foldr (updateNodeParents (Set.singleton ires)) g' (_nodeChildren node) -- set the parent node of the children to ires
                            in case findEquivalentNodeInDAG g node of
                                   Just i' -> (g & addedNodeIndices .~ (i':_addedNodeIndices g), i')
                                   Nothing -> (g'' & addedNodeIndices .~ (ires:_addedNodeIndices g''), ires)


-- Converts an Expr to an ExprDAGNode assuming some index.
-- If it already exists at a different index, having the same operator and the
-- same child indices, return that index.
addOpToDAG :: ExprDAG -> Expr -> [Int] -> (ExprDAG, Int)
addOpToDAG g (Sub t) [ich1, ich2] = let (g', ineg1) = addOpToDAG g (LInt (-1)) []
                                        (g'', imulneg1) = addOpToDAG g' (Mul t) [ineg1, ich2]
                                     in addOpToDAG g'' (Add t) [ich1, imulneg1] -- turn a-b to a + (-1)*b 
addOpToDAG g op ich = let (chset, itarget) = collapseCommAssoc g op ich 
                          nodeACCh = validACNodeCh $ reverse chset
                          nodeNormalCh = NNodeCh $ reverse ich
                          nodeEmptyCh = NCNodeCh
                          resACCh = (nodeACCh, itarget)
                          resNCh = (nodeEmptyCh, Just i)
                          i = _maxIndex g + 1
                          (nodech, iM) = case op of
                                            Mul _   -> resACCh
                                            Add _   -> resACCh
                                            And     -> resACCh
                                            Or      -> resACCh -- associative&commutative ops
                                            Eql _   -> resACCh -- equality is commutative but not associative, this is handled in collapseCommAssoc
                                            V _     -> resNCh  -- leaf/var
                                            LUnit   -> resNCh
                                            LBool _ -> resNCh
                                            LInt _  -> resNCh
                                            --LReal _ -> resNCh
                                            _       -> (nodeNormalCh, Just i) -- everything else
                          node = (emptyExprDAGNode & nodeOperator .~ op) & nodeChildren .~ nodech -- no parents initially, it will be set from parent node when it's reached
                          ires = fromMaybe i iM
                       in addNodeToDAG g ires node




-- First adds the Expr's operands to the ExprDAG, then the operator.
-- Returns a tuple of the new DAG and the inserted node's index.
--
-- If mholder holds an actual match, the expression is interpreted as
-- a match replacement, and vars names corresponding to var names in
-- mholder will be replaced with actual matches from g.
--
-- Otherwise, mholder is not used.
addExprToDAG :: MatchHolder Int -> Int -> ExprDAG -> Expr -> [Int] -> (ExprDAG, Int)
addExprToDAG mholder mnodei g (lhs :@ rhs) ich = let (g', childindex) = addExprToDAG mholder mnodei g rhs [] -- parse curr (right) child
                                                 in addExprToDAG mholder mnodei g' lhs (if childindex < 0 then ich else childindex:ich) -- recurse to left children and operator
addExprToDAG mholder mnodei g op ich = let (g', i') = addOpToDAG g op ich
                                           (NNodeCh mis) = _nodeChildren $ nodeAt g' mnodei
                                        in case op of
                                            (V v@(Var ('R':'l':_) _)) | _matched mholder && not (isRlMember v)                  -> (g, -1) -- not-matched Rl-s are not added as children!
                                            (V v)                     | _matched mholder && isRlMember v                        -> (g, mis !! (_matchedVals mholder ! (v & varType .~ Unit)))
                                            (V v)                     | _matched mholder && Map.member v (_matchedVals mholder) -> (g, mis !! (_matchedVals mholder ! v))
                                            (Mul _)                   | length ich == 1                                         -> (g, head ich)
                                            (Add _)                   | length ich == 1                                         -> (g, head ich)
                                            And                       | length ich == 1                                         -> (g, head ich)
                                            Or                        | length ich == 1                                         -> (g, head ich)
                                            _                                                                                   -> (g', i')
                              where isRlMember v@(Var ('R':'l':_) _) = Map.member (v & varType .~ Unit) (_matchedVals mholder)
                                    isRlMember _ = False

-- This is essentially a helper for replaceNodeWithExpr, but it can be used
-- individually. Replaces a node at index i with another node at index ir, and
-- then deletes the original node. All of i's parents will now point to ir.
replaceNodeInDAG :: ExprDAG -> Int -> Int -> ExprDAG
replaceNodeInDAG g i ir = let nodeparents = _nodeParents $ nodeAt g i
                              g' = foldr (\ip gc -> let pnode = nodeAt gc ip -- update pnode in its child's parents
                                                     in insertNodeToDAGAt gc ip (pnode & nodeChildren .~ replaceInCh (_nodeChildren pnode) i ir))
                                         g nodeparents
                              g'' = updateNodeParents nodeparents ir g'
                              finalg = removeNodeFromDAG g'' i
                           in if i /= ir
                                then if i == _rootIndex g then finalg & rootIndex .~ ir else finalg
                                else g''


-- Make all parents of i reference the top-level operator of the Expr instead.
-- Add these parents to the new Expr's top-level operator's node as well.
-- Then remove i
replaceNodeWithExpr :: MatchHolder Int -> Int -> ExprDAG -> Expr -> (ExprDAG, Int)
replaceNodeWithExpr mholder mnodei g e = let (g', i) = addExprToDAG mholder mnodei g e []
                                             g'' = replaceNodeInDAG g' (_matchedAt mholder) i
                                             newnode = nodeAt g'' i
                                          in case _nodeChildren newnode of
                                              ACNodeCh _ _ -> case _nodeOperator newnode of
                                                                Eql _ -> (g'', i) -- this is basically a custom collapseCommAssoc, so we don't handle Eql
                                                                _ -> foldr (\ip (gc, ic) -> let pnode = nodeAt gc ip -- merge the node's children into its parent where applicable, NOT MOVING the parent!
                                                                                                gc' = insertNodeToDAGAt gc ip (pnode & nodeChildren .~ makeCollapsedCh pnode newnode i)
                                                                                                gc'' = foldr (updateNodeParents (Set.singleton ip)) gc' (_nodeChildren newnode)
                                                                                                nodep = _nodeParents $ nodeAt gc'' i
                                                                                                gc''' = if Set.size nodep == 1 && Set.member ip nodep
                                                                                                          then removeNodeFromDAG gc'' i
                                                                                                          else insertNodeToDAGAt gc'' i (nodeAt gc'' i & nodeParents .~ Set.delete ip nodep)
                                                                                             in if _nodeOperator newnode == _nodeOperator pnode && i /= ip
                                                                                                  then (gc''' & addedNodeIndices .~ (ip:_addedNodeIndices gc'''), ip) else (gc, ic))
                                                                           (g'', i) (_nodeParents newnode) -- we don't consider rootIndex b.c. it wouldn't have eligible parents
                                              _          -> (g'', i)
    where makeCollapsedCh pnode newnode i = validACNodeCh $ nodeChToList (_nodeChildren pnode) >>= (\ic -> if ic == i then nodeChToList (_nodeChildren newnode) else [ic])
                                      

-- Parses an Expr into an ExprDAG, returns the ExprDAG and the variable count
-- (needed for heuristic which checks if we even need to try to replace).
parseExprToExprDAG :: Expr -> (ExprDAG, Int)
parseExprToExprDAG e = let (g, i) = addExprToDAG emptyMatchHolder (-1) emptyExprDAG e []
                        in (g & rootIndex .~ i, foldr (\(_, node) acc -> case _nodeOperator node of
                                                                                V _ -> acc + 1
                                                                                _   -> acc
                                                      ) 0 (Map.toList $ _nodesMap g))


-- Recursively converts a single ExprDAGNode (and its children) to an Expr.
convertSingleNodeToExpr :: ExprDAG -> Int -> Expr
convertSingleNodeToExpr g i = let node = nodeAt g i
                                  nodech = convertSingleNodeToExpr g <$> _nodeChildren node
                               in case nodeChToList nodech of
                                      []    -> _nodeOperator node
                                      [_]   -> _nodeOperator node :@ head (nodeChToList nodech)
                                      _     -> foldl1 (\rhs lhs -> _nodeOperator node :@ lhs :@ rhs) $ nodeChToList nodech


-- Converts an ExprDAG to an Expr.
convertExprDAGToExpr :: ExprDAG -> Expr
convertExprDAGToExpr g = convertSingleNodeToExpr g (_rootIndex g)


-- Applies a replacement to an Expr as described in the comments for
-- ReplacementRule.
replaceInExprDAG :: ReplacementRule -> ExprDAG -> Maybe ExprDAG
replaceInExprDAG (SingleReplacement p r) g = replacePatternInDAG p r g
replaceInExprDAG (SpeculativeReplacement r) g = Just $ fromMaybe g (replaceInExprDAG r g)
replaceInExprDAG (SequenceReplacement s) g = foldM (flip replaceInExprDAG) g s
replaceInExprDAG (LongestSequenceReplacement s) g = let (res, _, replaced) = foldr (\r (gc, done, replacedc) -> if done
                                                                                                                  then (gc, done, replacedc)
                                                                                                                  else let resc = replaceInExprDAG r gc
                                                                                                                        in (fromMaybe gc resc, isNothing resc, True))
                                                                                   (g, False, False) s
                                                     in if replaced then Just res else Nothing
replaceInExprDAG (AnyInSequenceReplacement s) g = let (n, g') = foldr countReplace (0, g) (reverse s)
                                                   in if n == 0 then Nothing else Just g'
                                                where countReplace :: ReplacementRule -> (Int, ExprDAG) -> (Int, ExprDAG)
                                                      countReplace r t@(i, g') = let res = replaceInExprDAG r g'
                                                                                  in if isNothing res then t else (i + 1, fromMaybe g' res)
replaceInExprDAG  r@(WhilePossibleReplacement s) g = replaceInExprDAGHelper r =<< replaceInExprDAG (AnyInSequenceReplacement s) g
                                                where replaceInExprDAGHelper :: ReplacementRule -> ExprDAG -> Maybe ExprDAG
                                                      replaceInExprDAGHelper r'@(WhilePossibleReplacement s') g' = let gM' = replaceInExprDAG (AnyInSequenceReplacement s') g'
                                                                                                                    in if isNothing gM' then Just g' else replaceInExprDAGHelper r' =<< gM'
                                                      replaceInExprDAGHelper r' g' = replaceInExprDAG r' g'
replaceInExprDAG (AlternateSingleReplacement l) g = fromMaybe Nothing $ find isJust $ map (`replaceInExprDAG` g) l


-- The values used by the heuristic which determines if we even need to
-- simplify.
{-maxNumVars, minNumNodes :: Int
maxNumVars = 9 
minNumNodes = 10
-}

-- Simplify an Expr using a given ReplacementRule.
replaceInExpr :: ReplacementRule -> Expr -> Maybe Expr
--replaceInExpr _ e | trace (show $ pretty e) False = undefined
replaceInExpr r e = let (g, _{-nvs-}) = parseExprToExprDAG e
                     in convertExprDAGToExpr <$> replaceInExprDAG r g --if nvs <= maxNumVars && Map.size (_nodesMap g) >= minNumNodes then convertExprDAGToExpr <$> replaceInExprDAG r g else Just e

-- Simplify an Expr using the default/main ReplacementRule.
-- Returns the same Expr if no replacements can be made.
simplifyExpr :: Expr -> Expr
simplifyExpr e = let g = fst $ parseExprToExprDAG e
                  in convertExprDAGToExpr $ fromMaybe g (replaceInExprDAG mainSimplifyRule g)

