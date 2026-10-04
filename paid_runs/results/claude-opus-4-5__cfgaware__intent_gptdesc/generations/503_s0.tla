---------------------------- MODULE Consensus ----------------------------

CONSTANT Value

VARIABLE chosen

TypeOK == chosen \subseteq Value

Init == chosen = {}

Propose(v) == /\ chosen = {}
              /\ v \in Value
              /\ chosen' = {v}

Learn == UNCHANGED chosen

Next == \/ \E v \in Value : Propose(v)
        \/ Learn

Spec == Init /\ [][Next]_chosen

FairSpec == Spec /\ WF_chosen(Next)

LiveSpec == FairSpec

Validity == \A v \in chosen : v \in Value

Agreement == Cardinality(chosen) <= 1

Integrity == [][chosen # {} => chosen' = chosen]_chosen

Safety == TypeOK /\ Validity /\ Agreement

EventualChoice == <>(chosen # {})

Liveness == EventualChoice

THEOREM Spec => []Safety

THEOREM LiveSpec => Liveness

==========================================================================