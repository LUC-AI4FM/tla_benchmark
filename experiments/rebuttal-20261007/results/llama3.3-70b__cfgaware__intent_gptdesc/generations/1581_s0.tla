---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES state, forks

state == [i \in 1..N |-> "thinking"]
forks == [i \in 1..N |-> FALSE]

Invariant == (* Mutual exclusion on forks *)
           /\ \A i \in 1..N : 
               state[i] = "eating" => 
               /\ forks[(i-1) % N + 1]
               /\ forks[i]
           /\ (* No two adjacent philosophers eating simultaneously *)
               state[i] = "eating" =>
               /\ state[(i-1) % N + 1] # "eating"
               /\ state[(i+1) % N + 1] # "eating"

StarvationFree == 
  <>[](\A i \in 1..N : <>(state[i] = "eating"))


Spec == 
  /\ state = [i \in 1..N |-> "thinking"]
  /\ forks = [i \in 1..N |-> FALSE]
  /\ [][
      \/ (\E i \in 1..N :
          /\ state[i] = "thinking"
          /\ state' = [state EXCEPT ![i] = "hungry"]
          /\ forks' = forks)
      \/ (\E i \in 1..N :
          /\ state[i] = "hungry"
          /\ forks[(i-1) % N + 1] = FALSE
          /\ forks[i] = FALSE
          /\ forks' = [forks EXCEPT ![(i-1) % N + 1] = TRUE, ![i] = TRUE]
          /\ state' = [state EXCEPT ![i] = "eating"])
      \/ (\E i \in 1..N :
          /\ state[i] = "eating"
          /\ forks' = [forks EXCEPT ![(i-1) % N + 1] = FALSE, ![i] = FALSE]
          /\ state' = [state EXCEPT ![i] = "thinking"])
      ]
  /\ WF_Vars(state, forks)

THEOREM Spec => []Invariant
THEOREM Spec => StarvationFree

=============================================================================