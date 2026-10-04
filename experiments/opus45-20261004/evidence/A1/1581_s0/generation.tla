---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N > 1

VARIABLES pc, sem

vars == <<pc, sem>>

Philosophers == 0..(N-1)

LeftFork(i) == i
RightFork(i) == (i + 1) % N

TypeOK ==
    /\ pc \in [Philosophers -> {"thinking", "hungry", "hasFirst", "eating"}]
    /\ sem \in [0..(N-1) -> {0, 1}]

Init ==
    /\ pc = [i \in Philosophers |-> "thinking"]
    /\ sem = [f \in 0..(N-1) |-> 1]

FirstFork(i) == IF i = 0 THEN LeftFork(i) ELSE RightFork(i)
SecondFork(i) == IF i = 0 THEN RightFork(i) ELSE LeftFork(i)

BecomeHungry(i) ==
    /\ pc[i] = "thinking"
    /\ pc' = [pc EXCEPT ![i] = "hungry"]
    /\ sem' = sem

PickUpFirstFork(i) ==
    /\ pc[i] = "hungry"
    /\ sem[FirstFork(i)] = 1
    /\ sem' = [sem EXCEPT ![FirstFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "hasFirst"]

PickUpSecondFork(i) ==
    /\ pc[i] = "hasFirst"
    /\ sem[SecondFork(i)] = 1
    /\ sem' = [sem EXCEPT ![SecondFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "eating"]

StopEating(i) ==
    /\ pc[i] = "eating"
    /\ sem' = [sem EXCEPT ![FirstFork(i)] = 1, ![SecondFork(i)] = 1]
    /\ pc' = [pc EXCEPT ![i] = "thinking"]

PhilosopherAction(i) ==
    \/ BecomeHungry(i)
    \/ PickUpFirstFork(i)
    \/ PickUpSecondFork(i)
    \/ StopEating(i)

Next == \E i \in Philosophers : PhilosopherAction(i)

Fairness == \A i \in Philosophers : SF_vars(PhilosopherAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Invariant ==
    \A i \in Philosophers :
        ~(pc[i] = "eating" /\ pc[(i + 1) % N] = "eating")

StarvationFree == \A i \in Philosophers : []<>(pc[i] = "eating")

=============================================================================