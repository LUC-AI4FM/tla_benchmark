------------------------------- MODULE MultiInstanceConsensus -------------------------------
EXTENDS TLC, FiniteSets

CONSTANTS Values, Slots

VARIABLES proposed, chosen

ASSUME /\ Cardinality(Values) > 0
       /\ Cardinality(Slots) > 0

Init == /\ proposed = {}
        /\ chosen = [s \in Slots |-> {}]

Propose ==
    \/ /\ EXISTS v \in Values \ proposed : proposed' = proposed \cup {v}
       /\ chosen' = chosen

Choose ==
    \/ /\ EXISTS s \in Slots, v \in proposed :
            /\ chosen[s] = {}
            /\ chosen' = [chosen EXCEPT ![s] = {v}]
           /\ proposed' = proposed

Next == Propose \/ Choose

Spec == Init /\ [][Next]_<<proposed, chosen>>

TypeOK ==
    /\ proposed \subseteq Values
    /\ \A s \in Slots : chosen[s] \subseteq Values

Nontriviality ==
    \A s \in Slots, v \in chosen[s] : v \in proposed

Stability ==
    \A s \in Slots, v \in chosen[s], <<proposed, chosen>>, <<proposed', chosen'>> \in Next :
        v \in chosen'[s]

Consistency ==
    \A s \in Slots : Cardinality(chosen[s]) <= 1

Liveness ==
    \A s \in Slots : <>(\E v \in Values : chosen[s] = {v})

LiveSpec == Spec /\ WF_<<proposed, chosen>>(Next)

=============================================================================