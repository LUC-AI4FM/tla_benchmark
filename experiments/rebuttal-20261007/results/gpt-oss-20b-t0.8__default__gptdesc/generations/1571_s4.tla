------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals, TLC

CONSTANT N
CONSTANT THINKING, FIRST, EATING

VARIABLES forks, state

(* Helper functions for fork indices *)
rightFork(i) == i
leftFork(i) == (i + N - 1) % N

firstFork(i) ==
  IF i = 0 THEN leftFork(0)
  ELSE rightFork(i)

secondFork(i) ==
  IF i = 0 THEN rightFork(0)
  ELSE leftFork(i)

(* Initial condition: all forks free, all philosophers thinking *)
Init == 
  /\ forks = [i \in 0..N-1 |-> TRUE]
  /\ state = [i \in 0..N-1 |-> THINKING]

(* Actions for acquiring first fork (order depends on philosopher) *)
AcquireFirst(i) ==
  /\ state[i] = THINKING
  /\ forks[firstFork(i)] = TRUE
  /\ forks' = [forks EXCEPT ![firstFork(i)] = FALSE]
  /\ state' = [state EXCEPT ![i] = FIRST]

(* Actions for acquiring second fork *)
AcquireSecond(i) ==
  /\ state[i] = FIRST
  /\ forks[secondFork(i)] = TRUE
  /\ forks' = [forks EXCEPT ![secondFork(i)] = FALSE]
  /\ state' = [state EXCEPT ![i] = EATING]

(* Action for eating and releasing both forks *)
Eat(i) ==
  /\ state[i] = EATING
  /\ forks' = [forks EXCEPT ![firstFork(i)] = TRUE, ![secondFork(i)] = TRUE]
  /\ state' = [state EXCEPT ![i] = THINKING]

(* Next-state relation: one philosopher performs one of the actions *)
Next == \E i \in 0..N-1 :
          (AcquireFirst(i) \/ AcquireSecond(i) \/ Eat(i))

(* Fairness requirement: each philosopher's actions are strongly fair *)
Fairness == \A i \in 0..N-1 : WF_vars(AcquireFirst(i) \/ AcquireSecond(i) \/ Eat(i))

(* Safety invariant: at most one philosopher may be eating simultaneously *)
NoTwoEating ==
  \A i, j \in 0..N-1 :
    (i # j) => ~(state[i] = EATING /\ state[j] = EATING)

(* Liveness property: each philosopher eventually eats infinitely often *)
InfinitelyOftenEating(i) == \Box\Diamond (state[i] = EATING)
StarvationFreedom == \A i \in 0..N-1 : InfinitelyOftenEating(i)

Spec == Init /\ [][Next]_<<forks, state>> /\ Fairness
       /\ NoTwoEating
       /\ StarvationFreedom

=============================================================================