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
  \/ \E s \in Slots, v \in proposed :
      /\ chosen[s] = {}
      /\ chosen' = [chosen EXCEPT ![s] = {v}]
      /\ UNCHANGED proposed

Spec ==
  Init /\ [][Next]_<<proposed, chosen>>

TypeCorrectness ==
  <<proposed, chosen>> \in [Values \cup (SUBSET Values)] <<Slots>>

NonTriviality ==
  proposed \subseteq Values

Stability ==
  proposed' = proposed

PerSlotConsistency ==
  \A s \in Slots : chosen[s] \subseteq proposed

Liveness ==
  <><s \in Slots, v \in proposed : chosen'[s] = {v}>_proposed, chosen

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []NonTriviality
THEOREM Spec => []Stability
THEOREM Spec => []PerSlotConsistency
THEOREM Spec => Liveness
```