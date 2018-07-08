# rewrite-simplifier
A highly configurable rewrite-rule simplifier for Quantifier-Free Linear Integer Arithmetic (QFLIA) formulas.

The simplifier allows the programmer to create decision trees to apply
pattern-based replacement rules to a QFLIA formula represented as an Abstract
Syntax Tree (AST). Think of it as regular expressions for QFLIA ASTs.

src/Formula/Simplifier.hs has detailed descriptions of these replacement rules,
as well as a "default" replacement rule which doubles as an illustrative
example.

All of my work is contained inside src/Formula/Simplifier.hs. It makes use of
the Expr type and a QuasiQuotes parser for it, both created by David Heath
(https://github.com/DAHeath) for use with the projects of the TrustAble
Programming (TAP) research group at the Georgia Institute of Technology
(https://www.cc.gatech.edu/~wharris/#research), for which I am currently an
undergraduate research assistant.

This simplifier was originally intended for use in optimizing and debugging
program safety provers, such as the ones being developed at TAP. These usecases
demanded for the configurablity - the replacement decision tree or decision trees
can very easily be modified or extended if the formulas encountered in a new
use-case turn out to have a different structure.

This is my first-ever Haskell project, and I would love some feedback!
