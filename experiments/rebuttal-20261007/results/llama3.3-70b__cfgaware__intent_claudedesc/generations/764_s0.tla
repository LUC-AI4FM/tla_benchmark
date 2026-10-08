--------------------------- MODULE DiningPhilosophers ---------------------------
EXTENDS Integers, Sequences

CONSTANT N
VARIABLES state, forks, requests

TypeOK == 
  /\ state \in [1..N -> {"hungry", "thinking", "eating"}]
  /\ forks \in [1..N -> {"clean", "dirty"}]
  /\ requests \in [1..N -> BOOLEAN]

Init ==
  /\ state = [i \in 1..N |-> "hungry"]
  /\ forks = [i \in 1..N |-> "dirty"]
  /\ requests = [i \in 1..N |-> FALSE]
  /\ forall i \in 1..N : 
      /\ (i < N) => forks[i] = "dirty"
      /\ (i = N) => forks[N] = "dirty"

Next(i) == 
  /\ IF state[i] = "hungry" 
    THEN 
      /\ state' = [state EXCEPT ![i] = "thinking"]
      /\ forks' = forks
      /\ requests' = [requests EXCEPT ![i] = TRUE]
    ELSE 
      /\ state' = [state EXCEPT ![i] = "eating"]
      /\ forks' = [forks EXCEPT ![i] = "clean", ![i+1 mod N] = "clean"]
      /\ requests' = [requests EXCEPT ![i] = FALSE, ![i+1 mod N] = FALSE]
  /\ IF state[i] = "thinking" 
    THEN 
      /\ state' = [state EXCEPT ![i] = "hungry"]
      /\ forks' = forks
      /\ requests' = [requests EXCEPT ![i] = FALSE]
    ELSE 
      /\ state' = [state EXCEPT ![i] = "eating"]
      /\ forks' = [forks EXCEPT ![i] = "dirty", ![i+1 mod N] = "dirty"]
      /\ requests' = [requests EXCEPT ![i] = TRUE, ![i+1 mod N] = TRUE]
  /\ IF state[i] = "eating" 
    THEN 
      /\ state' = [state EXCEPT ![i] = "thinking"]
      /\ forks' = forks
      /\ requests' = [requests EXCEPT ![i] = FALSE]

Next == 
  \/ \E i \in 1..N : Next(i)

Spec == 
  Init /\ [][Next]_<<state, forks, requests>>
=============================================================================