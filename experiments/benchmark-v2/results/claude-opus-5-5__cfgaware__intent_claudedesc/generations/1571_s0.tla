------------------------- MODULE DiningPhilosophers -------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

Procs == 0 .. (N - 1)

\* Fork i lies between philosopher i and philosopher (i+1) % N.
\* For philosopher p: left fork is fork p, right fork is fork (p+1) % N.
LeftFork(p)  == p
RightFork(p) == (p + 1) % N

\* Philosopher 0 acquires left first, then right;
\* all others acquire right first, then left.
FirstFork(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

VARIABLES forks, pc

vars == << forks, pc >>

TypeOK ==
    /\ forks \in [0 .. (N - 1) -> {0, 1}]
    /\ pc \in [Procs -> {"p1", "p2", "eat", "rel"}]

Init ==
    /\ forks = [f \in 0 .. (N - 1) |-> 1]   \* 1 = semaphore available
    /\ pc = [p \in Procs |-> "p1"]

\* P(first fork): blocks until available
AcquireFirst(self) ==
    /\ pc[self] = "p1"
    /\ forks[FirstFork(self)] > 0
    /\ forks' = [forks EXCEPT ![FirstFork(self)] = forks[FirstFork(self)] - 1]
    /\ pc' = [pc EXCEPT ![self] = "p2"]

\* P(second fork): blocks until available
AcquireSecond(self) ==
    /\ pc[self] = "p2"
    /\ forks[SecondFork(self)] > 0
    /\ forks' = [forks EXCEPT ![SecondFork(self)] = forks[SecondFork(self)] - 1]
    /\ pc' = [pc EXCEPT ![self] = "eat"]

\* Eating (critical section)
Eat(self) ==
    /\ pc[self] = "eat"
    /\ pc' = [pc EXCEPT ![self] = "rel"]
    /\ UNCHANGED forks

\* V both forks, then go back to thinking / trying again
Release(self) ==
    /\ pc[self] = "rel"
    /\ forks' = [forks EXCEPT ![LeftFork(self)]  = forks[LeftFork(self)] + 1,
                              ![RightFork(self)] = forks[RightFork(self)] + 1]
    /\ pc' = [pc EXCEPT ![self] = "p1"]

proc(self) ==
    \/ AcquireFirst(self)
    \/ AcquireSecond(self)
    \/ Eat(self)
    \/ Release(self)

Next == \E self \in Procs : proc(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs : SF_vars(proc(self))

-----------------------------------------------------------------------------

Eating(p) == pc[p] = "eat"

\* Mutual exclusion on forks: no two adjacent philosophers eat simultaneously.
MutualExclusion ==
    \A p \in Procs : ~(Eating(p) /\ Eating((p + 1) % N))

Invariant ==
    /\ TypeOK
    /\ MutualExclusion

\* Starvation freedom: every philosopher eats infinitely often.
StarvationFreedom ==
    \A p \in Procs : []<>(Eating(p))

THEOREM Spec => []Invariant
THEOREM Spec => StarvationFreedom
=============================================================================