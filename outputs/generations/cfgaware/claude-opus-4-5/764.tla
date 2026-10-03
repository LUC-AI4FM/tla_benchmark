---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N >= 2

Philosophers == 0..(N-1)

LeftFork(i) == i
RightFork(i) == (i + 1) % N

VARIABLES sem, pc

vars == <<sem, pc>>

TypeOK ==
    /\ sem \in [0..(N-1) -> {0, 1}]
    /\ pc \in [Philosophers -> {"thinking", "hungry", "hasFirst", "eating"}]

Init ==
    /\ sem = [f \in 0..(N-1) |-> 1]
    /\ pc = [p \in Philosophers |-> "thinking"]

\* Philosopher 0 acquires left fork first, then right fork
\* Philosophers 1 to N-1 acquire right fork first, then left fork

\* Philosopher becomes hungry (transition from thinking to hungry)
BecomeHungry(p) ==
    /\ pc[p] = "thinking"
    /\ pc' = [pc EXCEPT ![p] = "hungry"]
    /\ UNCHANGED sem

\* Philosopher 0: acquire left fork first
AcquireFirst0 ==
    /\ pc[0] = "hungry"
    /\ sem[LeftFork(0)] = 1
    /\ sem' = [sem EXCEPT ![LeftFork(0)] = 0]
    /\ pc' = [pc EXCEPT ![0] = "hasFirst"]

\* Philosopher 0: acquire right fork second
AcquireSecond0 ==
    /\ pc[0] = "hasFirst"
    /\ sem[RightFork(0)] = 1
    /\ sem' = [sem EXCEPT ![RightFork(0)] = 0]
    /\ pc' = [pc EXCEPT ![0] = "eating"]

\* Philosophers 1 to N-1: acquire right fork first
AcquireFirstOther(p) ==
    /\ p \in 1..(N-1)
    /\ pc[p] = "hungry"
    /\ sem[RightFork(p)] = 1
    /\ sem' = [sem EXCEPT ![RightFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "hasFirst"]

\* Philosophers 1 to N-1: acquire left fork second
AcquireSecondOther(p) ==
    /\ p \in 1..(N-1)
    /\ pc[p] = "hasFirst"
    /\ sem[LeftFork(p)] = 1
    /\ sem' = [sem EXCEPT ![LeftFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "eating"]

\* Philosopher finishes eating and releases both forks
FinishEating0 ==
    /\ pc[0] = "eating"
    /\ sem' = [sem EXCEPT ![LeftFork(0)] = 1, ![RightFork(0)] = 1]
    /\ pc' = [pc EXCEPT ![0] = "thinking"]

FinishEatingOther(p) ==
    /\ p \in 1..(N-1)
    /\ pc[p] = "eating"
    /\ sem' = [sem EXCEPT ![LeftFork(p)] = 1, ![RightFork(p)] = 1]
    /\ pc' = [pc EXCEPT ![p] = "thinking"]

\* Actions for philosopher 0
Action0 ==
    \/ BecomeHungry(0)
    \/ AcquireFirst0
    \/ AcquireSecond0
    \/ FinishEating0

\* Actions for philosophers 1 to N-1
ActionOther(p) ==
    \/ BecomeHungry(p)
    \/ AcquireFirstOther(p)
    \/ AcquireSecondOther(p)
    \/ FinishEatingOther(p)

\* Next-state relation
Next ==
    \/ Action0
    \/ \E p \in 1..(N-1) : ActionOther(p)

\* Strong fairness for each process
Fairness ==
    /\ SF_vars(Action0)
    /\ \A p \in 1..(N-1) : SF_vars(ActionOther(p))

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Mutual exclusion: adjacent philosophers never eat simultaneously
MutualExclusion ==
    \A p \in Philosophers : ~(pc[p] = "eating" /\ pc[(p + 1) % N] = "eating")

\* Starvation freedom: every philosopher eats infinitely often
StarvationFreedom ==
    \A p \in Philosophers : []<>(pc[p] = "eating")

===================================================================================