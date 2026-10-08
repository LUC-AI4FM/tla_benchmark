---------------------------- MODULE RandomFunctionSample ----------------------------
EXTENDS Integers, TLC

CONSTANT Domain, Codomain
VARIABLE functions

Domain == {1, 2, 3, 4, 5, 6, 7, 8, 9}
Codomain == {10, 11, 12, 13, 14, 15, 16, 17, 18, 19}

functions == RandomSubset([Domain -> Codomain], 1000)

Inv == functions \in SUBSET [Domain -> Codomain]

=============================================================================