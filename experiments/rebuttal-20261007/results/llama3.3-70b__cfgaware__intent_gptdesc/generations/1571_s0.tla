---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES philState, forkState

philState == [i \in 1..N |-> "thinking"]
forkState == [i \in 1..N |-> "free"]

Spec ==
  /\ philState = [i \in 1..N |-> "thinking"]
  /\ forkState = [i \in 1..N |-> "free"]
  /\ [][
      \/ \E i \in 1..N :
        /\ philState[i] = "thinking"
        /\ forkState[(i-1) % N + 1] = "free"
        /\ forkState[i] = "free"
        /\ philState' = [philState EXCEPT ![i] = "eating"]
        /\ forkState' = [forkState EXCEPT ![i] = "held", ![(i-1) % N + 1] = "held"]
      \/ \E i \in 1..N :
        /\ philState[i] = "eating"
        /\ philState' = [philState EXCEPT ![i] = "thinking"]
        /\ forkState' = [forkState EXCEPT ![i] = "free", ![(i-1) % N + 1] = "free"]
      \/ \E i \in 1..N :
        /\ philState[i] = "thinking"
        /\ philState' = [philState EXCEPT ![i] = "hungry"]
        /\ forkState' = forkState
      ]

Invariant ==
  /\ \A i \in 1..N : philState[i] \in {"thinking", "hungry", "eating"}
  /\ \A i \in 1..N : forkState[i] \in {"free", "held"}
  /\ \A i \in 1..N : ~(philState[i] = "eating" /\ philState[(i-1) % N + 1] = "eating")
  /\ \A i \in 1..N : ~(forkState[i] = "held" /\ forkState[(i-1) % N + 1] = "held")

===============================================================================