---------------------------- MODULE Consensus ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Values

VARIABLES chosen

TypeOK == chosen \subseteq Values

Init == chosen = {}

Choose(v) == /\ chosen = {}
             /\ v \in Values
             /\ chosen' = {v}

Next == \E v \in Values : Choose(v)

Spec == Init /\ [][Next]_chosen

FairSpec == Spec /\ WF_chosen(Next)

AtMostOneChosen == Cardinality(chosen) <= 1

Safety == [](AtMostOneChosen)

Liveness == <>(chosen # {})

THEOREM Spec => []TypeOK

THEOREM Spec => []AtMostOneChosen

THEOREM FairSpec => <>(chosen # {})

==========================================================================