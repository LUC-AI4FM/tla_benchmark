---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N >= 2

Philosophers == 0..(N-1)

VARIABLES sem, pc

vars == <<sem, pc>>

LeftFork(i) == i
RightFork(i) == (i + 1) % N

TypeOK ==
    /\ sem \in [0..(N-1) -> {0, 1}]
    /\ pc \in [Philosophers -> {"thinking", "hungry", "hasFirst", "eating"}]

Init ==
    /\ sem = [f \in 0..(N-1) |-> 1]
    /\ pc = [p \in Philosophers |-> "thinking"]

\* Philosopher 0: acquires left fork first, then right fork
BecomeHungry0 ==
    /\ pc[0] = "thinking"
    /\ pc' = [pc EXCEPT ![0] = "hungry"]
    /\ sem' = sem

AcquireFirst0 ==
    /\ pc[0] = "hungry"
    /\ sem[LeftFork(0)] = 1
    /\ sem' = [sem EXCEPT ![LeftFork(0)] = 0]
    /\ pc' = [pc EXCEPT ![0] = "hasFirst"]

AcquireSecond0 ==
    /\ pc[0] = "hasFirst"
    /\ sem[RightFork(0)] = 1
    /\ sem' = [sem EXCEPT ![RightFork(0)] = 0]
    /\ pc' = [pc EXCEPT ![0] = "eating"]

FinishEating0 ==
    /\ pc[0] = "eating"
    /\ sem' = [sem EXCEPT ![LeftFork(0)] = 1, ![RightFork(0)] = 1]
    /\ pc' = [pc EXCEPT ![0] = "thinking"]

Philosopher0 ==
    \/ BecomeHungry0
    \/ AcquireFirst0
    \/ AcquireSecond0
    \/ FinishEating0

\* Philosophers 1 to N-1: acquire right fork first, then left fork
BecomeHungryI(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "thinking"
    /\ pc' = [pc EXCEPT ![i] = "hungry"]
    /\ sem' = sem

AcquireFirstI(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "hungry"
    /\ sem[RightFork(i)] = 1
    /\ sem' = [sem EXCEPT ![RightFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "hasFirst"]

AcquireSecondI(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "hasFirst"
    /\ sem[LeftFork(i)] = 1
    /\ sem' = [sem EXCEPT ![LeftFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "eating"]

FinishEatingI(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "eating"
    /\ sem' = [sem EXCEPT ![LeftFork(i)] = 1, ![RightFork(i)] = 1]
    /\ pc' = [pc EXCEPT ![i] = "thinking"]

PhilosopherI(i) ==
    \/ BecomeHungryI(i)
    \/ AcquireFirstI(i)
    \/ AcquireSecondI(i)
    \/ FinishEatingI(i)

Next ==
    \/ Philosopher0
    \/ \E i \in 1..(N-1): PhilosopherI(i)

\* Strong fairness for each philosopher's actions
Fairness ==
    /\ SF_vars(Philosopher0)
    /\ \A i \in 1..(N-1): SF_vars(PhilosopherI(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual exclusion - adjacent philosophers never eat simultaneously
MutualExclusion ==
    \A i \in Philosophers:
        ~(pc[i] = "eating" /\ pc[(i + 1) % N] = "eating")

\* Liveness: Starvation freedom - every philosopher eats infinitely often
StarvationFreedom ==
    \A i \in Philosophers: []<>(pc[i] = "eating")

===================================================================================