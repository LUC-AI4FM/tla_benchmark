---------------------------- MODULE LargeStateSpace ----------------------------
EXTENDS Naturals, TLC

\* Domain and codomain sizes chosen to give a large but tractable state space.
\* Number of functions from a 6-element set to a 7-element set = 7^6 = 117649.
DomainSize   == 6
CodomainSize == 7

Domain   == 1..DomainSize
Codomain == 1..CodomainSize

ExpectedStates == CodomainSize ^ DomainSize

ASSUME PrintT(<<"Computing distinct states:", ExpectedStates>>)

VARIABLE x

vars == <<x>>

\* Initial state: any function from Domain to Codomain
Init == x \in [Domain -> Codomain]

\* The system is static once initialized
Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

\* Trivially true type invariant
Inv == x \in [Domain -> Codomain]

=============================================================================