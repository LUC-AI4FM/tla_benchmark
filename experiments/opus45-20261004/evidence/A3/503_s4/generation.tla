---------------------------- MODULE Consensus ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Values

VARIABLES chosen

TypeOK == chosen \subseteq Values

Init == chosen = {}

Choose(v) == 
    /\ chosen = {}
    /\ v \in Values
    /\ chosen' = {v}

Next == \E v \in Values : Choose(v)

Spec == Init /\ [][Next]_chosen

LiveSpec == Spec /\ WF_chosen(Next)

AtMostOneChosen == Cardinality(chosen) <= 1

SafetyInvariant == TypeOK /\ AtMostOneChosen

EventuallyChosen == <>(chosen # {})

THEOREM Spec => []SafetyInvariant

THEOREM LiveSpec => EventuallyChosen

==========================================================================