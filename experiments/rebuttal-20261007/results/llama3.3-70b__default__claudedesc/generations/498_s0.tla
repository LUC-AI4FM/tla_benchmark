```
MODULE MultiInstanceConsensus
EXTENDS Integers, FiniteSets

CONSTANTS Values, Slots

VARIABLES proposed, chosen

Init ==
  /\ proposed = {}
  /\ chosen = [s \in Slots |-> {}]

Propose ==
  /\ ~proposed = Values
  /\ proposed' = proposed \cup {v \in Values : v \notin proposed}
  /\ chosen' = chosen

Choose ==
  /\ \exists s \in Slots : chosen[s] = {}
  /\ \exists v \in proposed : chosen' = [chosen EXCEPT ![s] = {v}]
  /\ proposed' = proposed

Next ==
  \/ Propose
  \/ Choose
  \/ (proposed' = proposed /\ chosen' = chosen)

Spec == Init /\ [][Next]_<<proposed, chosen>>

LiveSpec == Spec /\ WF_(Propose) /\ WF_(Choose)

TypeOK == chosen \in [Slots -> SUBSET Values]
Nontriviality == \A s \in Slots : chosen[s] \subseteq proposed
Stability == \A s \in Slots : chosen[s] = {} \/ chosen'[s] = chosen[s]
Consistency == \A s \in Slots : Cardinality(chosen[s]) <= 1

Liveness == <>[\A s \in Slots : chosen[s] /= {}]_chosen

THEOREM Spec => []TypeOK
THEOREM Spec => []Nontriviality
THEOREM Spec => []Stability
THEOREM Spec => []Consistency
THEOREM LiveSpec => Liveness

INSTANCE ModelChecking WITH Values <- {1, 2}, Slots <- {a, b}
```
Note: The `WF_` operator is used to specify weak fairness. The `<>` operator is used to specify "eventually". The `[Next]_<<proposed, chosen>>` expression specifies that the next state is determined by the `Propose` and `Choose` actions, which modify the `proposed` and `chosen` variables.