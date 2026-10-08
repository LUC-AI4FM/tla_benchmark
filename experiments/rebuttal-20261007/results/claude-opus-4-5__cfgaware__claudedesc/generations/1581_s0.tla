---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals, Sequences

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES sem, pc

vars == <<sem, pc>>

Philosophers == 0..(N-1)

PCStates == {"thinking", "hungry1", "hungry2", "eating", "release1", "release2"}

TypeInvariant ==
    /\ sem \in [0..(N-1) -> {0, 1}]
    /\ pc \in [Philosophers -> PCStates]

Init ==
    /\ sem = [i \in 0..(N-1) |-> 1]
    /\ pc = [p \in Philosophers |-> "thinking"]

\* Right fork index for philosopher p
RightFork(p) == p

\* Left fork index for philosopher p
LeftFork(p) == (p - 1) % N

\* Philosopher 0 acquires forks in opposite order (left first, then right)
\* to break symmetry and prevent deadlock

\* For philosopher 0: first fork is left (N-1), second fork is right (0)
\* For philosophers 1 to N-1: first fork is right (self), second fork is left ((self-1) mod N)

FirstFork(p) == IF p = 0 THEN N - 1 ELSE p
SecondFork(p) == IF p = 0 THEN 0 ELSE (p - 1) % N

\* Transition: thinking -> hungry1 (try to acquire first fork)
Think(p) ==
    /\ pc[p] = "thinking"
    /\ pc' = [pc EXCEPT ![p] = "hungry1"]
    /\ sem' = sem

\* Transition: hungry1 -> hungry2 (acquire first fork when available)
AcquireFirst(p) ==
    /\ pc[p] = "hungry1"
    /\ sem[FirstFork(p)] = 1
    /\ sem' = [sem EXCEPT ![FirstFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "hungry2"]

\* Transition: hungry2 -> eating (acquire second fork when available)
AcquireSecond(p) ==
    /\ pc[p] = "hungry2"
    /\ sem[SecondFork(p)] = 1
    /\ sem' = [sem EXCEPT ![SecondFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "eating"]

\* Transition: eating -> release1 (start releasing forks)
Eat(p) ==
    /\ pc[p] = "eating"
    /\ pc' = [pc EXCEPT ![p] = "release1"]
    /\ sem' = sem

\* Transition: release1 -> release2 (release first fork)
ReleaseFirst(p) ==
    /\ pc[p] = "release1"
    /\ sem' = [sem EXCEPT ![FirstFork(p)] = 1]
    /\ pc' = [pc EXCEPT ![p] = "release2"]

\* Transition: release2 -> thinking (release second fork)
ReleaseSecond(p) ==
    /\ pc[p] = "release2"
    /\ sem' = [sem EXCEPT ![SecondFork(p)] = 1]
    /\ pc' = [pc EXCEPT ![p] = "thinking"]

\* All actions for a philosopher
PhilosopherActions(p) ==
    \/ Think(p)
    \/ AcquireFirst(p)
    \/ AcquireSecond(p)
    \/ Eat(p)
    \/ ReleaseFirst(p)
    \/ ReleaseSecond(p)

Next == \E p \in Philosophers : PhilosopherActions(p)

\* Strong fairness for each philosopher's actions
Fairness == \A p \in Philosophers : SF_vars(PhilosopherActions(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: No two adjacent philosophers eat simultaneously
\* Adjacent means they share a fork (philosopher p and (p+1) mod N share fork p)
Invariant ==
    \A p \in Philosophers :
        ~(pc[p] = "eating" /\ pc[(p + 1) % N] = "eating")

\* Liveness: Every philosopher eats infinitely often
StarvationFree ==
    \A p \in Philosophers : []<>(pc[p] = "eating")

===================================================================================