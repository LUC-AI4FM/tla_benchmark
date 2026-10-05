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

FairSpec == Spec /\ WF_chosen(Next)

\* Safety invariant: at most one value is ever chosen
AtMostOneChosen == Cardinality(chosen) <= 1

\* Alternative formulation of safety
SafetyInvariant == chosen = {} \/ \E v \in Values : chosen = {v}

\* Liveness property: eventually some value is chosen
EventuallyChosen == <>(chosen # {})

\* Theorems
THEOREM Spec => []AtMostOneChosen

THEOREM Spec => []SafetyInvariant

THEOREM FairSpec => EventuallyChosen

==========================================================================