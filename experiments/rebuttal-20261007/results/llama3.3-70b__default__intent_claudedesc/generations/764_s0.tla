```
MODULE DiningPhilosophers
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES forks, states, requests

Init ==
  /\ forks \in [1..N -> {"owner" : Int, "clean" : Bool}]
  /\ states \in [1..N -> {"state" : {"hungry", "thinking", "eating"}}]
  /\ requests \in [1..N -> BOOLEAN]
  /\ forall i \in 1..N :
      /\ forks[i].owner = IF i = 1 THEN 1 ELSE (i - 1)
      /\ forks[i].clean = FALSE
      /\ states[i].state = "thinking"
      /\ requests[i] = FALSE

Next ==
  \/ \E i \in 1..N :
    /\ states[i].state = "hungry"
    /\ forks[(i - 1) % N + 1].owner = i
    /\ forks[i].owner = i
    /\ forks[(i - 1) % N + 1].clean
    /\ forks[i].clean
    /\ states' = [states EXCEPT ![i].state = "eating"]
    /\ forks' = forks
    /\ requests' = requests
  \/ \E i \in 1..N :
    /\ states[i].state = "eating"
    /\ states' = [states EXCEPT ![i].state = "thinking"]
    /\ forks' = [forks EXCEPT
                 ![i].clean = FALSE
                 ![(i - 1) % N + 1].clean = FALSE]
    /\ requests' = requests
  \/ \E i \in 1..N :
    /\ states[i].state = "thinking"
    /\ requests[i] = TRUE
    /\ states' = [states EXCEPT ![i].state = "hungry"]
    /\ forks' = forks
    /\ requests' = [requests EXCEPT ![i] = FALSE]
  \/ \E i \in 1..N :
    /\ requests[(i - 1) % N + 1]
    /\ forks[i].owner = (i - 1) % N + 1
    /\ states' = states
    /\ forks' = [forks EXCEPT ![i].owner = i, ![(i - 1) % N + 1].clean = TRUE]
    /\ requests' = [requests EXCEPT ![(i - 1) % N + 1] = FALSE]

Spec ==
  /\ Init
  /\ [][Next]_forks, states, requests
  /\ WF_vars(Next, forks, states, requests)

TypeInvariant ==
  /\ forks \in [1..N -> {"owner" : Int, "clean" : Bool}]
  /\ states \in [1..N -> {"state" : {"hungry", "thinking", "eating"}}]
  /\ requests \in [1..N -> BOOLEAN]

MutualExclusionInvariant ==
  /\ forall i, j \in 1..N :
      ~ (states[i].state = "eating" /\ states[j].state = "eating"
         /\ (i = (j - 1) % N + 1 \/ i = (j + 1) % N))

THEOREM Spec => []TypeInvariant
THEOREM Spec => []MutualExclusionInvariant

Fairness ==
  /\ WF_vars(Next, forks, states, requests)
```
Note: The `WF_vars` operator is used to specify weak fairness for the variables. This ensures that every philosopher gets a chance to eat infinitely often.