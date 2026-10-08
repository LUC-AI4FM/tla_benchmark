```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES forks, states

Init ==
  /\ forks \in [1..N -> {"free", "held"}]
  /\ states \in [1..N -> {"thinking", "hungry", "eating"}]
  /\ forks = [i \in 1..N |-> "free"]
  /\ states = [i \in 1..N |-> "thinking"]

Next ==
  \/ \E i \in 1..N :
    /\ states[i] = "thinking"
    /\ states' = [states EXCEPT ![i] = "hungry"]
    /\ forks' = forks
  \/ \E i \in 1..N :
    /\ states[i] = "hungry"
    /\ forks[(i-1) % N + 1] = "free"
    /\ forks[i] = "free"
    /\ forks' = [forks EXCEPT ![(i-1) % N + 1] = "held", ![i] = "held"]
    /\ states' = [states EXCEPT ![i] = "eating"]
  \/ \E i \in 1..N :
    /\ states[i] = "eating"
    /\ forks' = [forks EXCEPT ![(i-1) % N + 1] = "free", ![i] = "free"]
    /\ states' = [states EXCEPT ![i] = "thinking"]

Spec ==
  Init /\ [][Next]_<<forks, states>>

SafetyInv ==
  \A i, j \in 1..N : 
    ~(states[i] = "eating" /\ states[j] = "eating" /\ (j = (i-1) % N + 1 \/ j = (i % N) + 1))

DeadlockFree ==
  <>(\A i \in 1..N : states[i] = "thinking")

StarvationFreedom ==
  \A i \in 1..N :
    []<>states[i] = "eating"

ResourceIntegrity ==
  /\ \A i, j \in 1..N : 
      ~(forks[i] = "held" /\ forks[j] = "held" /\ (j = (i-1) % N + 1 \/ j = (i % N) + 1))
  /\ \A i \in 1..N :
      []<>(forks[i] = "free")

THEOREM Spec => []SafetyInv
THEOREM Spec => DeadlockFree
THEOREM Spec => StarvationFreedom
THEOREM Spec => ResourceIntegrity

FAIRNESS Next
```