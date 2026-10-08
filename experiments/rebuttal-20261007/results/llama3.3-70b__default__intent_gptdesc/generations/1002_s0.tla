```
MODULE BarrierSynchronization
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES round, phases, arrived

Init ==
  /\ round = 0
  /\ phases \in [1..N -> {"arrive", "release"}]
  /\ arrived = {}

Next ==
  \/ \E i \in (1..N) :
      /\ phases[i] = "arrive"
      /\ phases' = [phases EXCEPT ![i] = "release"]
      /\ round' = round
      /\ arrived' = arrived \cup {i}
  \/ (\A i \in (1..N) : i \in arrived)
     /\ phases' = [i \in (1..N) |-> "arrive"]
     /\ round' = round + 1
     /\ arrived' = {}

Spec ==
  Init /\ [][Next]_<<round, phases, arrived>>

TypeInvariant ==
  /\ round \in Nat
  /\ phases \in [1..N -> {"arrive", "release"}]
  /\ arrived \subseteq (1..N)

SafetyInvariant ==
  \A i \in (1..N) : phases[i] = "release" => \A j \in (1..N) : j \in arrived

LivenessProperty ==
  <>[\A i \in (1..N) : i \in arrived]_arrived
  => <>(\A i \in (1..N) : phases[i] = "release")_phases

Fairness ==
  WF_vars(Next, <<round, phases, arrived>>)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyInvariant
THEOREM Spec => LivenessProperty
```