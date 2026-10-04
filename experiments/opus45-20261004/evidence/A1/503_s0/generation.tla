------------------------------ MODULE Consensus ------------------------------

CONSTANT Values

VARIABLE chosen

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Values : chosen' = {v}

Spec == Init /\ [][Next]_chosen

LiveSpec == Spec /\ WF_chosen(Next)

TypeOK == chosen \subseteq Values

Safety == Cardinality(chosen) <= 1

Liveness == <>(chosen # {})

THEOREM Spec => []Safety

=============================================================================