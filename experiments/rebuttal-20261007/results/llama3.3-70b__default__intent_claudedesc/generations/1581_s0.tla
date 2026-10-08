```
MODULE DiningPhilosophers
EXTENDS Integers, Sequences

CONSTANTS N

VARIABLES forks, states

Init ==
  /\ forks = [i \in 1..N |-> 1]
  /\ states = [i \in 1..N |-> "thinking"]

Next ==
  \/ \E i \in 1..N :
    /\ states[i] = "thinking"
    /\ (i # N) => forks[(i + 1) % N] = 1
    /\ forks[i] = 1
    /\ states' = [states EXCEPT ![i] = "eating"]
    /\ forks' = [forks EXCEPT ![i] = 0, ![(i + 1) % N] = 0]
  \/ \E i \in 1..N :
    /\ states[i] = "eating"
    /\ states' = [states EXCEPT ![i] = "thinking"]
    /\ forks' = [forks EXCEPT ![i] = 1, ![(i + 1) % N] = 1]
  \/ \E i \in 1..N :
    /\ states[i] = "thinking"
    /\ (i = N) => forks[1] = 1
    /\ forks[(i + N - 1) % N] = 1
    /\ states' = [states EXCEPT ![i] = "eating"]
    /\ forks' = [forks EXCEPT ![(i + N - 1) % N] = 0, ![i] = 0]

Spec ==
  /\ Init
  /\ [][Next]_<<forks, states>>
  /\ WF_(states, [i \in 1..N |-> "thinking" -> "eating"]) 
  /\ SF_(states, [i \in 1..N |-> "thinking" -> "eating"])

THEOREM Spec => []~( \E i \in 1..N : states[i] = "eating" /\ states[(i + 1) % N] = "eating")
THEOREM Spec => <>[]<>(states[1] = "eating") 
```