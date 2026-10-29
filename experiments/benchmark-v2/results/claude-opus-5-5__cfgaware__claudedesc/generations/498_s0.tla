----------------------------- MODULE MultiConsensus -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Values, Slots

ASSUME Values # {}
ASSUME Slots # {}

VARIABLES proposed, chosen

vars == <<proposed, chosen>>

Init ==
    /\ proposed = {}
    /\ chosen = [s \in Slots |-> {}]

Propose ==
    \E v \in Values \ proposed :
        /\ proposed' = proposed \cup {v}
        /\ UNCHANGED chosen

Choose ==
    \E s \in Slots :
        /\ chosen[s] = {}
        /\ \E v \in proposed :
              chosen' = [chosen EXCEPT ![s] = {v}]
        /\ UNCHANGED proposed

Next == Propose \/ Choose

Spec == Init /\ [][Next]_vars

LiveSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------------------------

TypeOK ==
    /\ proposed \subseteq Values
    /\ chosen \in [Slots -> SUBSET Values]
    /\ \A s \in Slots : IsFiniteSet(chosen[s])

Nontriviality ==
    \A s \in Slots : chosen[s] \subseteq proposed

Stability ==
    \A s \in Slots : \A v \in Values :
        [](v \in chosen[s] => [](v \in chosen[s]))

Consistency ==
    \A s \in Slots : Cardinality(chosen[s]) <= 1

Liveness ==
    \A s \in Slots : <>(chosen[s] # {})

THEOREM Spec => []TypeOK
THEOREM Spec => []Nontriviality
THEOREM Spec => Stability
THEOREM Spec => []Consistency
THEOREM LiveSpec => Liveness

=============================================================================