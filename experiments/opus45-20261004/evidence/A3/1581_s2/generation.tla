---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N

ASSUME N >= 2

Philosophers == 0..(N-1)

VARIABLES pc, sem

vars == <<pc, sem>>

TypeOK ==
    /\ pc \in [Philosophers -> {"thinking", "hungry", "has_first", "eating"}]
    /\ sem \in [Philosophers -> {0, 1}]

LeftFork(i) == i
RightFork(i) == (i + 1) % N

FirstFork(i) ==
    IF i = 0 THEN LeftFork(i) ELSE RightFork(i)

SecondFork(i) ==
    IF i = 0 THEN RightFork(i) ELSE LeftFork(i)

Init ==
    /\ pc = [i \in Philosophers |-> "thinking"]
    /\ sem = [f \in Philosophers |-> 1]

BecomeHungry(i) ==
    /\ pc[i] = "thinking"
    /\ pc' = [pc EXCEPT ![i] = "hungry"]
    /\ sem' = sem

AcquireFirstFork(i) ==
    /\ pc[i] = "hungry"
    /\ sem[FirstFork(i)] = 1
    /\ sem' = [sem EXCEPT ![FirstFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "has_first"]

AcquireSecondFork(i) ==
    /\ pc[i] = "has_first"
    /\ sem[SecondFork(i)] = 1
    /\ sem' = [sem EXCEPT ![SecondFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "eating"]

FinishEating(i) ==
    /\ pc[i] = "eating"
    /\ sem' = [sem EXCEPT ![LeftFork(i)] = 1, ![RightFork(i)] = 1]
    /\ pc' = [pc EXCEPT ![i] = "thinking"]

PhilosopherAction(i) ==
    \/ BecomeHungry(i)
    \/ AcquireFirstFork(i)
    \/ AcquireSecondFork(i)
    \/ FinishEating(i)

Next == \E i \in Philosophers : PhilosopherAction(i)

Fairness ==
    \A i \in Philosophers :
        /\ SF_vars(BecomeHungry(i))
        /\ SF_vars(AcquireFirstFork(i))
        /\ SF_vars(AcquireSecondFork(i))
        /\ SF_vars(FinishEating(i))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A i \in Philosophers :
        ~(pc[i] = "eating" /\ pc[(i + 1) % N] = "eating")

StarvationFreedom ==
    \A i \in Philosophers : []<>(pc[i] = "eating")

===================================================================================