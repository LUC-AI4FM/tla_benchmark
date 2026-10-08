---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences

CONSTANTS N

ASSUME N \in Nat /\ N > 1

Philosophers == 0..(N-1)

(* Each philosopher can be in one of these states *)
States == {"thinking", "hungry_first", "hungry_second", "eating"}

VARIABLES
    state,      \* state[p] is the current state of philosopher p
    forks       \* forks[f] = TRUE means fork f is available (semaphore is 1)

vars == <<state, forks>>

(* Fork indices: fork i is between philosopher i and philosopher (i+1) mod N *)
(* Philosopher p's left fork is p, right fork is (p-1+N) mod N *)

LeftFork(p) == p
RightFork(p) == (p - 1 + N) % N

(* For philosopher 0: picks left first, then right (opposite order) *)
(* For philosophers 1 to N-1: picks right first, then left *)

FirstFork(p) == IF p = 0 THEN LeftFork(p) ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

TypeOK ==
    /\ state \in [Philosophers -> States]
    /\ forks \in [Philosophers -> BOOLEAN]

Init ==
    /\ state = [p \in Philosophers |-> "thinking"]
    /\ forks = [f \in Philosophers |-> TRUE]

(* Philosopher starts to get hungry and tries to acquire first fork *)
StartHungry(p) ==
    /\ state[p] = "thinking"
    /\ forks[FirstFork(p)] = TRUE
    /\ state' = [state EXCEPT ![p] = "hungry_first"]
    /\ forks' = [forks EXCEPT ![FirstFork(p)] = FALSE]

(* Philosopher has first fork and tries to acquire second fork *)
AcquireSecond(p) ==
    /\ state[p] = "hungry_first"
    /\ forks[SecondFork(p)] = TRUE
    /\ state' = [state EXCEPT ![p] = "hungry_second"]
    /\ forks' = [forks EXCEPT ![SecondFork(p)] = FALSE]

(* Philosopher has both forks and starts eating *)
StartEating(p) ==
    /\ state[p] = "hungry_second"
    /\ state' = [state EXCEPT ![p] = "eating"]
    /\ UNCHANGED forks

(* Philosopher finishes eating and releases both forks *)
FinishEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ forks' = [forks EXCEPT ![LeftFork(p)] = TRUE, ![RightFork(p)] = TRUE]

(* All actions for a philosopher *)
PhilosopherAction(p) ==
    \/ StartHungry(p)
    \/ AcquireSecond(p)
    \/ StartEating(p)
    \/ FinishEating(p)

Next == \E p \in Philosophers : PhilosopherAction(p)

(* Strong fairness for each philosopher's complete process *)
Fairness == \A p \in Philosophers :
    /\ SF_vars(StartHungry(p))
    /\ SF_vars(AcquireSecond(p))
    /\ SF_vars(StartEating(p))
    /\ SF_vars(FinishEating(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(* Safety: Mutual exclusion - no two adjacent philosophers eat simultaneously *)
MutualExclusion ==
    \A p \in Philosophers :
        ~(state[p] = "eating" /\ state[(p + 1) % N] = "eating")

(* Alternative formulation: a fork is held by at most one eating philosopher *)
ForkMutualExclusion ==
    \A f \in Philosophers :
        ~(state[f] = "eating" /\ state[(f + 1) % N] = "eating")

(* Liveness: Every philosopher eats infinitely often (starvation freedom) *)
StarvationFreedom == \A p \in Philosophers : []<>(state[p] = "eating")

(* Deadlock freedom: some philosopher can always make progress *)
DeadlockFreedom == []<><<Next>>_vars

(* Invariants for model checking *)
Invariant == TypeOK /\ MutualExclusion

===================================================================================