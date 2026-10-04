---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N

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

BeginHungry(p) ==
    /\ pc[p] = "thinking"
    /\ pc' = [pc EXCEPT ![p] = "hungry"]
    /\ sem' = sem

AcquireFirst(p) ==
    /\ pc[p] = "hungry"
    /\ IF p = 0
       THEN /\ sem[LeftFork(p)] = 1
            /\ sem' = [sem EXCEPT ![LeftFork(p)] = 0]
       ELSE /\ sem[RightFork(p)] = 1
            /\ sem' = [sem EXCEPT ![RightFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "hasFirst"]

AcquireSecond(p) ==
    /\ pc[p] = "hasFirst"
    /\ IF p = 0
       THEN /\ sem[RightFork(p)] = 1
            /\ sem' = [sem EXCEPT ![RightFork(p)] = 0]
       ELSE /\ sem[LeftFork(p)] = 1
            /\ sem' = [sem EXCEPT ![LeftFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "eating"]

FinishEating(p) ==
    /\ pc[p] = "eating"
    /\ sem' = [sem EXCEPT ![LeftFork(p)] = 1, ![RightFork(p)] = 1]
    /\ pc' = [pc EXCEPT ![p] = "thinking"]

PhilosopherAction(p) ==
    \/ BeginHungry(p)
    \/ AcquireFirst(p)
    \/ AcquireSecond(p)
    \/ FinishEating(p)

Next ==
    \E p \in Philosophers : PhilosopherAction(p)

Fairness ==
    \A p \in Philosophers : SF_vars(PhilosopherAction(p))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

MutualExclusion ==
    \A p \in Philosophers : ~(pc[p] = "eating" /\ pc[(p + 1) % N] = "eating")

StarvationFreedom ==
    \A p \in Philosophers : []<>(pc[p] = "eating")

===================================================================================