\* --------------------------------------------------------------------
\*  Dining Philosophers (N = 4)
\*  Specification in TLA+
\* --------------------------------------------------------------------

MODULE DiningPhilosophers
EXTENDS Naturals, Integers

CONSTANT N

VARIABLES State, Forks

(* Enumerated philosopher states *)
PhilosopherStates == {"thinking", "first_acquired", "eating"}

(* Initial state: all philosophers thinking, all forks free (-1) *)
Init ==
  /\ State \in [0..N-1 -> PhilosopherStates]
  /\ Forks \in [0..N-1 -> 0..N-1 \/ {-1}]
  /\ \A i \in 0..N-1 : State[i] = "thinking"
  /\ \A f \in 0..N-1 : Forks[f] = -1

(* Helper functions for fork indices *)
LeftFork(i) == i
RightFork(i) == Mod(i + 1, N)

FirstFork(i) ==
  IF i = 0 THEN LeftFork(i)
  ELSE RightFork(i)

SecondFork(i) ==
  IF i = 0 THEN RightFork(i)
  ELSE LeftFork(i)

(* Acquire the first fork (left for philosopher 0, right otherwise) *)
AcquireFirst(i) ==
  /\ i \in 0..N-1
  /\ State[i] = "thinking"
  /\ Forks[FirstFork(i)] = -1
  /\ State' = [State EXCEPT ![i] = "first_acquired"]
  /\ Forks' = [Forks EXCEPT ![FirstFork(i)] = i]

(* Acquire the second fork and transition to eating *)
AcquireSecond(i) ==
  /\ i \in 0..N-1
  /\ State[i] = "first_acquired"
  /\ Forks[SecondFork(i)] = -1
  /\ State' = [State EXCEPT ![i] = "eating"]
  /\ Forks' = [Forks EXCEPT ![SecondFork(i)] = i]

(* Release both forks after eating *)
Release(i) ==
  /\ i \in 0..N-1
  /\ State[i] = "eating"
  /\ Forks[FirstFork(i)] = i
  /\ Forks[SecondFork(i)] = i
  /\ State' = [State