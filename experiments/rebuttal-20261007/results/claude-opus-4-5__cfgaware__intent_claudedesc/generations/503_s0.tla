---------------------------- MODULE Consensus ----------------------------

CONSTANT Values

VARIABLE chosen

Init == chosen = {}

Choose(v) == 
    /\ chosen = {}
    /\ v \in Values
    /\ chosen' = {v}

Next == \E v \in Values : Choose(v)

Spec == Init /\ [][Next]_chosen

LiveSpec == Spec /\ WF_chosen(Next)

TypeOK == 
    /\ chosen \subseteq Values
    /\ IsFiniteSet(chosen)
    /\ Cardinality(chosen) <= 1

Safety == TypeOK

Liveness == <>(chosen # {})

THEOREM Spec => []Safety

THEOREM LiveSpec => Liveness

=========================================================================