---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS N

ASSUME N \in Nat /\ N > 1

Philosophers == 0..(N-1)

LeftFork(p) == p
RightFork(p) == (p + 1) % N

(* 
   States for each philosopher:
   - "thinking": not holding any forks
   - "hungry_first": waiting to acquire first fork
   - "hungry_second": holding first fork, waiting for second
   - "eating": holding both forks
*)

VARIABLES
    state,      \* state[p] \in {"thinking", "hungry_first", "hungry_second", "eating"}
    forks       \* forks[f] = -1 (free) or philosopher id holding it

vars == <<state, forks>>

TypeOK ==
    /\ state \in [Philosophers -> {"thinking", "hungry_first", "hungry_second", "eating"}]
    /\ forks \in [Philosophers -> Philosophers \cup {-1}]

(* 
   Fork acquisition order:
   - Philosopher 0 picks up LEFT fork first, then RIGHT fork
   - All other philosophers pick up RIGHT fork first, then LEFT fork
   This asymmetry breaks the circular wait condition
*)

FirstFork(p) == IF p = 0 THEN LeftFork(p) ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

Init ==
    /\ state = [p \in Philosophers |-> "thinking"]
    /\ forks = [f \in Philosophers |-> -1]

(* Philosopher becomes hungry and tries to get first fork *)
BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry_first"]
    /\ UNCHANGED forks

(* Philosopher acquires first fork *)
AcquireFirstFork(p) ==
    /\ state[p] = "hungry_first"
    /\ forks[FirstFork(p)] = -1
    /\ forks' = [forks EXCEPT ![FirstFork(p)] = p]
    /\ state' = [state EXCEPT ![p] = "hungry_second"]

(* Philosopher acquires second fork and starts eating *)
AcquireSecondFork(p) ==
    /\ state[p] = "hungry_second"
    /\ forks[SecondFork(p)] = -1
    /\ forks' = [forks EXCEPT ![SecondFork(p)] = p]
    /\ state' = [state EXCEPT ![p] = "eating"]

(* Philosopher finishes eating, releases both forks *)
FinishEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ forks' = [forks EXCEPT ![FirstFork(p)] = -1, ![SecondFork(p)] = -1]

(* All actions for a single philosopher *)
PhilosopherAction(p) ==
    \/ BecomeHungry(p)
    \/ AcquireFirstFork(p)
    \/ AcquireSecondFork(p)
    \/ FinishEating(p)

Next == \E p \in Philosophers : PhilosopherAction(p)

(* Strong fairness for each philosopher's complete action set *)
Fairness == \A p \in Philosophers : SF_vars(PhilosopherAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* SAFETY PROPERTY: No two adjacent philosophers eat simultaneously *)

MutualExclusion ==
    \A p \in Philosophers :
        ~(state[p] = "eating" /\ state[(p + 1) % N] = "eating")

(* Alternative formulation: each fork is held by at most one philosopher *)
ForkMutualExclusion ==
    \A f \in Philosophers :
        forks[f] /= -1 => 
            \A p \in Philosophers : 
                (forks[f] = p) => (f = FirstFork(p) \/ f = SecondFork(p))

(* LIVENESS PROPERTY: Every philosopher eats infinitely often (starvation freedom) *)
StarvationFreedom == \A p \in Philosophers : []<>(state[p] = "eating")

=============================================================================