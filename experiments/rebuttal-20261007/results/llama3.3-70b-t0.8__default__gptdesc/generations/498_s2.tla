```
MODULE MultiSlotConsensus
EXTENDS Integers, FiniteSets

CONSTANTS Slots, Values
VARIABLES proposed, chosen

Init ==
  /\ proposed = {}
  /\ chosen = [s \in Slots |-> {}]

Next ==
  \/ \E v \in Values :
      /\ v \notin proposed
      /\ proposed' = proposed \cup {v}
      /\ UNCHANGED chosen
  \/ \E s \in Slots :
      /\ chosen[s] = {}
      /\ \E v \in proposed :
          /\ chosen' = [chosen EXCEPT ![s] = {v}]
          /\ UNCHANGED proposed

Spec ==
  /\ Init
  /\ [][Next]_proposed \* [][Next]_chosen
  /\ WF_vars(Next)

TypeCorrectness == proposed \subseteq Values
NonTriviality == proposed /= {}
Stability == proposed' = proposed
PerSlotConsistency == \A s \in Slots : chosen[s] \subseteq proposed

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []NonTriviality
THEOREM Spec => []Stability
THEOREM Spec => []PerSlotConsistency
THEOREM Spec => <>[]\A s \in Slots : chosen[s] /= {}
```