------------------------------- MODULE FiniteStateSystem -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS DomainSize
ASSUME DomainSize >= 3

VARIABLES state, mapping

DOMAIN == {1, 2, 3, 4, 5}
INDEX_DOMAIN == 1..DomainSize

Init == /\ state \in DOMAIN
        /\ mapping \in [INDEX_DOMAIN -> DOMAIN]

Next ==
    \/ /\ state' = state
       /\ mapping' \in [INDEX_DOMAIN -> DOMAIN]
    \/ /\ state' \in DOMAIN
       /\ mapping' \in [INDEX_DOMAIN -> DOMAIN]

Spec ==
    /\ Init
    /\ [][Next]_<<state, mapping>>

StateInvariant ==
    \E i \in INDEX_DOMAIN : mapping[i] = state

DeadlockFree ==
    [](\/ state' \in DOMAIN)

TypeOK ==
    /\ state \in DOMAIN
    /\ mapping \in [INDEX_DOMAIN -> DOMAIN]

SpecWithInvariants ==
    Spec /\ StateInvariant /\ DeadlockFree /\ TypeOK

=============================================================================