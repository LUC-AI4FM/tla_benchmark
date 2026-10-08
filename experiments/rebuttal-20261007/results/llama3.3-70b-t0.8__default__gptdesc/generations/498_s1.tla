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
  /\ Init
  /\ [][Next]_proposed \* [][Next]_chosen

TypeCorrectness ==
  proposed \subseteq Values

NonTriviality ==
  Slots /= {}

Stability ==
  \A s \in Slots : chosen[s] = {} \/ chosen[s] \subseteq proposed

PerSlotConsistency ==
  \A s \in Slots, v1, v2 \in Values :
    /\ {v1} = chosen[s]
    /\ {v2} = chosen[s]
    ==> v1 = v2

Liveness == <>[]\A s \in Slots : chosen[s] /= {}

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []NonTriviality
THEOREM Spec => []Stability
THEOREM Spec => []PerSlotConsistency
THEOREM Spec /\ WF_vars(Next) => Liveness
```