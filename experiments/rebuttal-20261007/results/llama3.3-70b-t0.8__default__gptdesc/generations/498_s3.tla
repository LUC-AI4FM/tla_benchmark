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
  /\ [][Next]_<<proposed, chosen>>
  /\ WF_<<proposed, chosen>>(Next)

TypeCorrectness ==
  /\ proposed \subseteq Values
  /\ \A s \in Slots : chosen[s] \subseteq Values

NonTriviality ==
  /\ proposed \neq {}
  /\ \A s \in Slots : chosen[s] \neq {}

Stability ==
  /\ \A v \in proposed :
      \/ \E s \in Slots : v \in chosen[s]
      \/ ~\E s \in Slots : chosen[s] = {}

PerSlotConsistency ==
  /\ \A s \in Slots :
      /\ \A v1, v2 \in chosen[s] : v1 = v2
      /\ \A v \in chosen[s] : v \in proposed

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []NonTriviality
THEOREM Spec => []Stability
THEOREM Spec => []PerSlotConsistency
THEOREM Spec => <><\A s \in Slots : chosen[s] # {}>
```