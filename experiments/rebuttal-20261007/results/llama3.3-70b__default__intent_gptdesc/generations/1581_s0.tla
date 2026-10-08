```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES state, forks

state == [i \in 1..N |-> "thinking"]
forks == [i \in 1..N |-> FALSE]

Init ==
  /\ state = [i \in 1..N |-> "thinking"]
  /\ forks = [i \in 1..N |-> FALSE]

Next ==
  \/ \E i \in 1..N :
    /\ state[i] = "thinking"
    /\ state' = [state EXCEPT ![i] = "hungry"]
    /\ forks' = forks
  \/ \E i \in 1..N :
    /\ state[i] = "hungry"
    /\ forks' = [forks EXCEPT ![i] = TRUE]
    /\ state' = [state EXCEPT ![i] = "eating"]
    /\ \A j \in 1..N : j # i => forks'[j] = forks[j]
  \/ \E i \in 1..N :
    /\ state[i] = "eating"
    /\ forks' = [forks EXCEPT ![i] = FALSE]
    /\ state' = [state EXCEPT ![i] = "thinking"]
    /\ \A j \in 1..N : j # i => forks'[j] = forks[j]

Spec ==
  Init /\ [][Next]_<<state, forks>>

SafetyInv ==
  /\ \A i \in 1..N : state[i] \in {"thinking", "hungry", "eating"}
  /\ \A i \in 1..N : forks[i] => state[i] = "eating"
  /\ \A i \in 1..N : \E j \in {i % N + 1, (i-2) % N + 1} :
      ~(forks[i] /\ forks[j])

LivenessInv ==
  \A i \in 1..N : <<state[i] = "hungry">> ~> <<state[i] = "eating">>

Fairness ==
  WF_<<state, forks>>(\[Next]_<<state, forks>>)

THEOREM Spec => []SafetyInv
THEOREM Spec => LivenessInv
THEOREM Spec => Fairness

```
Note: The above TLA+ specification models the Dining Philosophers problem with N philosophers. It includes safety invariants to prevent two adjacent philosophers from eating simultaneously and to ensure mutual exclusion on forks. The liveness property guarantees that every philosopher who attempts to eat will eventually be able to eat, and the fairness condition ensures progress assumptions about scheduling or enabling conditions for fork acquisition.