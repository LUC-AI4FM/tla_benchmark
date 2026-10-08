------------------------------- MODULE FiniteStateSystem -------------------------------

CONSTANTS 
    StateDomain,          \* The set {1, 2, 3, 4, 5}
    MappingDomain         \* A finite domain with at least three indices

VARIABLES 
    state,                \* Current state of the system
    mapping               \* Abstract mapping from MappingDomain to StateDomain

ASSUME 
    StateDomain = {1, 2, 3, 4, 5}
    Cardinality(MappingDomain) >= 3

Init == /\ state \in StateDomain
        /\ mapping \in [MappingDomain -> StateDomain]

Next ==
    \/ /\ state' = state
       /\ mapping' \in [MappingDomain -> StateDomain]
    \/ /\ state' \in StateDomain
       /\ mapping' \in [MappingDomain -> StateDomain]

Spec == Init /\ [][Next]_<<state, mapping>>

\* Invariant: At least one index in the mapping's domain maps to the current state
Inv ==
    \E i \in MappingDomain : mapping[i] = state

\* Liveness property: Always has at least one enabled transition
Live ==
    \/ state' = state
    \/ state' \in StateDomain

THEOREM Spec => []Inv /\ <>[]Live

=============================================================================