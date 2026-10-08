------------------------------- MODULE ConsensusSystem -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Values, Slots
ASSUME /\ Cardinality(Values) = 2
       /\ Cardinality(Slots) = 2

VARIABLES proposed, chosen

Init == /\ proposed \in [Slots -> {}]
        /\ chosen \in [Slots -> {}]

Next ==
    \/ \E s \in Slots, v \in Values :
         /\ proposed' = [proposed EXCEPT ![s] = proposed[s] \cup {v}]
         /\ chosen' = chosen
    \/ \E s \in Slots, v \in proposed[s] \ (chosen[s]) :
         /\ proposed' = proposed
         /\ chosen' = [chosen EXCEPT ![s] = chosen[s] \cup {v}]

Spec ==
    /\ Init
    /\ [][Next]_<<proposed, chosen>>
    /\ WF_next(<<proposed, chosen>>)

TypeInvariant == 
    /\ \A s \in Slots : proposed[s] \subseteq Values
    /\ \A s \in Slots : chosen[s] \subseteq Values

Nontriviality ==
    /\ \A s \in Slots : chosen[s] \subseteq proposed[s]

Stability ==
    /\ \A s \in Slots, v1, v2 \in chosen[s] : v1 = v2

Consistency ==
    /\ \A s \in Slots : Cardinality(chosen[s]) <= 1

Liveness ==
    /\ \A s \in Slots : <>[](Cardinality(chosen[s]) > 0)

THEOREM Spec => []TypeInvariant
THEOREM Spec => [](Nontriviality)
THEOREM Spec => [](Stability)
THEOREM Spec => [](Consistency)
THEOREM Spec => <>(Liveness)

=============================================================================