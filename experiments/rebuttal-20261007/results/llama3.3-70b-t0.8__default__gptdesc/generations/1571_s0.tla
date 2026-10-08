```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES forks, state, eaten

Init ==
  /\ forks = [i \in 1..N |-> 0]
  /\ state = [i \in 1..N |-> "thinking"]
  /\ eaten = [i \in 1..N |-> 0]

Next ==
  \/ \E i \in 1..N :
    /\ state[i] = "thinking"
    /\ forks[(i+1) % N] = 0
    /\ (i = 1 \/ i = 0)
    /\ forks[i] = 0
    /\ state' = [state EXCEPT ![i] = "hungry"]
    /\ forks' = [forks EXCEPT ![i] = 1]
    /\ eaten' = eaten
  \/ \E i \in 1..N :
    /\ state[i] = "thinking"
    /\ forks[(i+1) % N] = 0
    /\ (i > 1 /\ i < N)
    /\ forks[(i-1+N)%N] = 0
    /\ state' = [state EXCEPT ![i] = "hungry"]
    /\ forks' = [forks EXCEPT ![(i-1+N)%N] = 1]
    /\ eaten' = eaten
  \/ \E i \in 1..N :
    /\ state[i] = "hungry"
    /\ (i > 0 /\ i < N)
    /\ forks[i] = 1
    /\ forks[(i-1+N)%N] = 1
    /\ state' = [state EXCEPT ![i] = "eating"]
    /\ forks' = forks
    /\ eaten' = [eaten EXCEPT ![i] = eaten[i] + 1]
  \/ \E i \in 1..N :
    /\ state[i] = "hungry"
    /\ (i = 0)
    /\ forks[(i-1+N)%N] = 1
    /\ forks[i] = 1
    /\ state' = [state EXCEPT ![i] = "eating"]
    /\ forks' = forks
    /\ eaten' = [eaten EXCEPT ![i] = eaten[i] + 1]
  \/ \E i \in 1..N :
    /\ state[i] = "eating"
    /\ state' = [state EXCEPT ![i] = "thinking"]
    /\ forks' = [forks EXCEPT ![i] = 0, ![(i-1+N)%N] = 0]
    /\ eaten' = eaten

Spec ==
  Init /\ [][Next]_<<forks, state, eaten>>
  /\ WF_(state, <<1..N>>)
  /\ SF_(state, <<1..N>>)

EatingInvariant ==
  \A i \in 1..N : (state[i] = "eating") => ((forks[i] = 1) /\ (forks[(i-1+N)%N] = 1))

StarvationFreedom ==
  \A i \in 1..N : <<state[i] = "thinking">> ~> <<state[i] = "eating">>

THEOREM Spec => []EatingInvariant
THEOREM Spec => StarvationFreedom
```