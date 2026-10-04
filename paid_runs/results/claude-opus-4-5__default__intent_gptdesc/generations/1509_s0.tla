---------------------------- MODULE FiniteStateSystem ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS
    StateSet,       \* The finite set {1,2,3,4,5}
    IndexDomain     \* The finite domain with three or more indices

VARIABLES
    state,          \* The current state value
    mapping         \* Abstract total mapping from IndexDomain to StateSet

vars == <<state, mapping>>

ASSUME StateSetAssumption == StateSet = {1, 2, 3, 4, 5}
ASSUME IndexDomainAssumption == /\ IsFiniteSet(IndexDomain)
                                 /\ Cardinality(IndexDomain) >= 3

TypeInvariant ==
    /\ state \in StateSet
    /\ mapping \in [IndexDomain -> StateSet]

MappingCoversState ==
    \E idx \in IndexDomain : mapping[idx] = state

SafetyInvariant ==
    /\ TypeInvariant
    /\ MappingCoversState

Init ==
    /\ state \in StateSet
    /\ mapping \in [IndexDomain -> StateSet]
    /\ \E idx \in IndexDomain : mapping[idx] = state

Next ==
    /\ \E newState \in StateSet :
        /\ \E newMapping \in [IndexDomain -> StateSet] :
            /\ \E idx \in IndexDomain : newMapping[idx] = newState
            /\ state' = newState
            /\ mapping' = newMapping

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

AlwaysEnabled == ENABLED Next

LivenessProperty == []AlwaysEnabled

=============================================================================