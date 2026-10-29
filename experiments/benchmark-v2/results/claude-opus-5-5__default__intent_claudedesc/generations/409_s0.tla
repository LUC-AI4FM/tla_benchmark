---------------------------- MODULE LargeStateSpace ----------------------------
EXTENDS Naturals, TLC

CONSTANTS DomainSize, CodomainSize

ASSUME DomainSize \in Nat /\ DomainSize >= 1
ASSUME CodomainSize \in Nat /\ CodomainSize >= 1

Domain   == 1..DomainSize
Codomain == 1..CodomainSize

RECURSIVE Pow(_, _)
Pow(b, e) == IF e = 0 THEN 1 ELSE b * Pow(b, e - 1)

ExpectedStates == Pow(CodomainSize, DomainSize)

ASSUME PrintT(<<"Computing all functions; expected number of states:", ExpectedStates>>)

VARIABLE f

vars == <<f>>

TypeOK == f \in [Domain -> Codomain]

Init == f \in [Domain -> Codomain]

Next == UNCHANGED f

Spec == Init /\ [][Next]_vars

\* Trivial safety properties
TrivialInvariant == TRUE

FunctionWellFormed ==
    /\ DOMAIN f = Domain
    /\ \A d \in Domain : f[d] \in Codomain

\* The state never changes once initialized
Static == [][UNCHANGED f]_vars

THEOREM Spec => []TypeOK
=============================================================================