```
MODULE DiningPhilosophers
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES forks, state

Init == (forks = [i \in 1..N |-> TRUE] /\ 
         state = [i \in 1..N |-> "thinking"])

Next == 
  (\E i \in 1..N : 
     (state[i] = "thinking") /\ 
     (forks[(i+1) % N] = TRUE) /\ 
     ((i # 1) => (forks[i] = TRUE)) /\ 
     ((i = 1) => (forks[N] = TRUE))) /\ 
   (\E j \in 1..N : 
      state' = [state EXCEPT ![j] = IF (j = i) THEN "eating" ELSE @) /\ 
      forks' = [forks EXCEPT ![i % N + 1] = FALSE, ![i] = FALSE])

Spec == Init /\ [][Next]_<<forks, state>>
Fairness == \A i \in 1..N : WF(Next, <<forks, state>>)

EatingInvariant == [](\A i \in 1..N : state[i] = "eating" => forks[(i+1) % N] = FALSE)
StarvationFreedom == <>[]\A i \in 1..N : state[i] = "thinking"

THEOREM Spec => []EatingInvariant /\ StarvationFreedom
```