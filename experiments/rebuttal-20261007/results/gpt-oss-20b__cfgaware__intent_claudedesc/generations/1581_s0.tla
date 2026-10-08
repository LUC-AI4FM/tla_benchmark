------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals

CONSTANT N

VARIABLES forks, state

PHILOSOPHERS == 1..N
FORKS          == PHILOSOPHERS

leftFork(i)   == IF i = 1 THEN N ELSE i-1
rightFork(i)  == i
nextIndex(i)  == IF i < N THEN i+1 ELSE 1

(* Initial state *)
Init ==
  /\ forks = [i \in FORKS |-> TRUE]
  /\ state = [i \in PHILOSOPHERS |-> "Thinking"]

(* Actions *)

FirstFork(i) ==
  /\ state[i] = "Thinking"
  /\ IF i = 1 THEN forks[N] = TRUE ELSE forks[i] = TRUE
  /\ forks'   = [forks EXCEPT ![IF i=1 THEN N ELSE i] = FALSE]
  /\ state'   = [state EXCEPT ![i] = IF i=1 THEN "HungryLeft" ELSE "HungryRight"]

SecondFork(i) ==
  /\ state[i] = IF i=1 THEN "HungryLeft" ELSE "HungryRight"
  /\ IF i = 1 THEN forks[i] = TRUE ELSE forks[N] = TRUE
  /\ forks'   = [forks EXCEPT ![IF i=1 THEN i ELSE N] = FALSE]
  /\ state'   = [state EXCEPT ![i] = "Eating"]

Release(i) ==
  /\ state[i] = "Eating"
  /\ forks'   = [forks EXCEPT ![rightFork(i)] = TRUE, ![leftFork(i)] = TRUE]
  /\ state'   = [state EXCEPT ![i] = "Thinking"]

Next == 
  \E i \in PHILOSOPHERS :
    (FirstFork(i) \/ SecondFork(i) \/ Release(i))

Spec == Init /\ [][Next]_<<forks, state>>

(* Safety invariant: no two adjacent philosophers eat simultaneously *)
Invariant ==
  \A i \in PHILOSOPHERS : 
    IF state[i] = "Eating" THEN state[nextIndex(i)] # "Eating" ELSE TRUE

(* Liveness property: every philosopher eats infinitely often *)
StarvationFree == 
  \A i \in PHILOSOPHERS : []<> (state[i] = "Eating")

=============================================================================