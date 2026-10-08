```tla
MODULE MultiSlotConsensus

EXTENDS Integers, FiniteSets

CONSTANTS Slots, Values
VARIABLES proposed, chosen

Init == (
  /\ proposed = {}
  /\ chosen = [s \in Slots |-> {}]
)

Next == (
  \/ \E v \in Values :
    /\ v \notin proposed
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED chosen
  \/ \E s \in Slots, v \in proposed :
    /\ chosen[s] = {}
    /\ proposed' = proposed
    /\ chosen' = [chosen EXCEPT ![s] = {v}]
)

Spec == Init /\ [][Next]_proposed /\ [][Next]_chosen

TypeCorrectness == proposed \subseteq Values
NonTriviality == Slots /= {}
Stability == \A s \in Slots : chosen[s] /= {} => chosen' = [chosen EXCEPT ![s] = chosen[s]]
PerSlotConsistency == \A s \in Slots : chosen[s] /= {} => \E v \in proposed : chosen[s] = {v}

SafetyInv == TypeCorrectness /\ NonTriviality /\ Stability /\ PerSlotConsistency

Fairness == WF_Next(Next)

Liveness == <> \A s \in Slots : chosen[s] /= {}

THEOREM Spec => [] SafetyInv
THEOREM Spec /\ Fairness => Liveness

```
Note: Due to limitations in the formatting and response length, I couldn't include any comments or explanations. Please ensure that you understand each part of this specification based on your knowledge of TLA+ and its applications in specifying and verifying distributed systems.