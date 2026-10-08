---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 1

Philosophers == 0..(N-1)

LeftFork(p) == p
RightFork(p) == (p + 1) % N

VARIABLES pc, forks

vars == <<pc, forks>>

TypeOK ==
    /\ pc \in [Philosophers -> {"thinking", "hungry_first", "hungry_second", "eating"}]
    /\ forks \in [0..(N-1) -> {-1} \cup Philosophers]

Init ==
    /\ pc = [p \in Philosophers |-> "thinking"]
    /\ forks = [f \in 0..(N-1) |-> -1]

FirstFork(p) == IF p = 0 THEN LeftFork(p) ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

BecomeHungry(p) ==
    /\ pc[p] = "thinking"
    /\ pc' = [pc EXCEPT ![p] = "hungry_first"]
    /\ UNCHANGED forks

PickUpFirstFork(p) ==
    /\ pc[p] = "hungry_first"
    /\ forks[FirstFork(p)] = -1
    /\ forks' = [forks EXCEPT ![FirstFork(p)] = p]
    /\ pc' = [pc EXCEPT ![p] = "hungry_second"]

PickUpSecondFork(p) ==
    /\ pc[p] = "hungry_second"
    /\ forks[SecondFork(p)] = -1
    /\ forks' = [forks EXCEPT ![SecondFork(p)] = p]
    /\ pc' = [pc EXCEPT ![p] = "eating"]

FinishEating(p) ==
    /\ pc[p] = "eating"
    /\ forks' = [forks EXCEPT ![LeftFork(p)] = -1, ![RightFork(p)] = -1]
    /\ pc' = [pc EXCEPT ![p] = "thinking"]

PhilosopherAction(p) ==
    \/ BecomeHungry(p)
    \/ PickUpFirstFork(p)
    \/ PickUpSecondFork(p)
    \/ FinishEating(p)

Next == \E p \in Philosophers : PhilosopherAction(p)

Fairness ==
    \A p \in Philosophers :
        /\ SF_vars(BecomeHungry(p))
        /\ SF_vars(PickUpFirstFork(p))
        /\ SF_vars(PickUpSecondFork(p))
        /\ SF_vars(FinishEating(p))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A p \in Philosophers :
        ~(pc[p] = "eating" /\ pc[(p + 1) % N] = "eating")

Invariant == MutualExclusion

StarvationFree == \A p \in Philosophers : []<>(pc[p] = "eating")

===================================================================================