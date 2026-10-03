---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES forks, state

state == [i \in 0..N-1 |-> "thinking"]
forks == [i \in 0..N-1 |-> FALSE]

Invariant == (* Mutual exclusion: at most one philosopher is eating *)
           \A i \in 0..N-1 : state[i] = "eating" => 
             \A j \in 0..N-1 : i # j => state[j] # "eating"

Spec == 
  /\ (* Initialize states and forks *)
     state = [i \in 0..N-1 |-> "thinking"]
     /\ forks = [i \in 0..N-1 |-> FALSE]
  /\ [][* Next-state relation *]
  /\ WF_vars(state, forks)

Next(i \in 0..N-1) == 
  IF state[i] = "thinking" THEN
    (* Try to pick up right fork (or left fork for philosopher 0) *)
    IF i = 0 THEN
      /\ forks[(i+1) % N] = FALSE
      /\ forks' = [forks EXCEPT ![(i+1) % N] = TRUE]
      /\ state' = [state EXCEPT !i = "right_fork"]
    ELSE
      /\ forks[i] = FALSE
      /\ forks' = [forks EXCEPT !i = TRUE]
      /\ state' = [state EXCEPT !i = "right_fork"]
  ELSE IF state[i] = "right_fork" THEN
    (* Try to pick up left fork (or right fork for philosopher 0) *)
    IF i = 0 THEN
      /\ forks[i] = FALSE
      /\ forks' = [forks EXCEPT !i = TRUE]
      /\ state' = [state EXCEPT !i = "eating"]
    ELSE
      /\ forks[(i+1) % N] = FALSE
      /\ forks' = [forks EXCEPT ![(i+1) % N] = TRUE]
      /\ state' = [state EXCEPT !i = "eating"]
  ELSE IF state[i] = "eating" THEN
    (* Put down both forks *)
    /\ forks' = [j \in 0..N-1 |-> FALSE]
    /\ state' = [state EXCEPT !i = "thinking"]
  ELSE
    TRUE

THEOREM Spec => []Invariant
=============================================================================