---------------------------- MODULE Consensus ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Values

VARIABLES chosen

TypeOK == chosen \subseteq Values /\ IsFiniteSet(chosen)

Init == chosen = {}

Choose(v) == 
    /\ chosen = {}
    /\ v \in Values
    /\ chosen' = {v}

Next == \E v \in Values : Choose(v)

Spec == Init /\ [][Next]_chosen

FairSpec == Spec /\ WF_chosen(Next)

Safety == 
    /\ chosen \subseteq Values
    /\ IsFiniteSet(chosen)
    /\ Cardinality(chosen) <= 1

Liveness == <>(chosen # {})

==========================================================================