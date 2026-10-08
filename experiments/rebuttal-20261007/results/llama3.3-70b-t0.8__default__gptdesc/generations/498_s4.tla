```
MODULE MultiSlotConsensus
EXTENDS Integers, FiniteSets

CONSTANTS Slots, Values
VARIABLES proposed, chosen

Init ==
  /\ proposed = {}
  /\ chosen = [s \in Slots |-> {}]

Next ==
  /\ ( proposer ==>> 
        /\ proposed' = proposed \cup {v}
        /\ v \in Values
        /\ v \notin proposed
        /\ UNCHANGED chosen )
    \/ ( picker ==>> 
          /\ \E s \in Slots, v \in proposed :
              /\ chosen' = [chosen EXCEPT ![s] = {v}]
              /\ chosen'[s] = {v}
              /\ UNCHANGED proposed )
  /\ WeakFairness(proposer)
  /\ WeakFairness(picker)

Spec == Init /\ [][Next]_<<proposed, chosen>>
TypeCorrectness == proposed \subseteq Values
Nontriviality == Slots /= {}
Stability == ( chosen' = chosen ) \/ (\E s \in Slots : chosen'[s] = {})
PerSlotConsistency == \A s \in Slots : 
                        ( \E v \in proposed : chosen[s] = {v} ) \/ ( chosen[s] = {} )
Liveness == <>[]\A s \in Slots : chosen[s] /= {}

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []Nontriviality
THEOREM Spec => []Stability
THEOREM Spec => []PerSlotConsistency
THEOREM Spec => Liveness
```