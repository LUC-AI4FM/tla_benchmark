---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N > 1

Philosophers == 0..(N-1)

VARIABLES sem, pc

vars == <<sem, pc>>

\* Each philosopher has a left and right fork
\* Philosopher i's left fork is i, right fork is (i+1) % N
LeftFork(i) == i
RightFork(i) == (i + 1) % N

\* Program counter states for each philosopher:
\* "thinking" - philosopher is thinking
\* "hungry" - philosopher wants to eat, hasn't acquired any fork yet
\* "hasFirst" - philosopher has acquired first fork, waiting for second
\* "eating" - philosopher has both forks and is eating

TypeOK == /\ sem \in [0..(N-1) -> {0, 1}]
          /\ pc \in [Philosophers -> {"thinking", "hungry", "hasFirst", "eating"}]

Init == /\ sem = [f \in 0..(N-1) |-> 1]
        /\ pc = [p \in Philosophers |-> "thinking"]

\* Philosopher becomes hungry
BecomeHungry(p) ==
    /\ pc[p] = "thinking"
    /\ pc' = [pc EXCEPT ![p] = "hungry"]
    /\ UNCHANGED sem

\* Philosopher 0 acquires left fork first (breaks symmetry)
\* Philosophers 1 to N-1 acquire right fork first
FirstFork(p) == IF p = 0 THEN LeftFork(p) ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

\* Acquire first fork
AcquireFirst(p) ==
    /\ pc[p] = "hungry"
    /\ sem[FirstFork(p)] = 1
    /\ sem' = [sem EXCEPT ![FirstFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "hasFirst"]

\* Acquire second fork
AcquireSecond(p) ==
    /\ pc[p] = "hasFirst"
    /\ sem[SecondFork(p)] = 1
    /\ sem' = [sem EXCEPT ![SecondFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "eating"]

\* Philosopher finishes eating, releases both forks
FinishEating(p) ==
    /\ pc[p] = "eating"
    /\ sem' = [sem EXCEPT ![LeftFork(p)] = 1, ![RightFork(p)] = 1]
    /\ pc' = [pc EXCEPT ![p] = "thinking"]

\* All actions for philosopher p
PhilosopherAction(p) ==
    \/ BecomeHungry(p)
    \/ AcquireFirst(p)
    \/ AcquireSecond(p)
    \/ FinishEating(p)

Next == \E p \in Philosophers : PhilosopherAction(p)

\* Strong fairness for each philosopher's actions
Fairness == \A p \in Philosophers : SF_vars(PhilosopherAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual exclusion - adjacent philosophers never eat simultaneously
\* Two philosophers are adjacent if they share a fork
MutualExclusion ==
    \A p \in Philosophers : 
        ~(pc[p] = "eating" /\ pc[(p + 1) % N] = "eating")

\* Liveness: Starvation freedom - every philosopher eats infinitely often
StarvationFreedom ==
    \A p \in Philosophers : []<>(pc[p] = "eating")

===================================================================================