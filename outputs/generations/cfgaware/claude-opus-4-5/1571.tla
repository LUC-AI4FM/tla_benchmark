---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES pc, forks

vars == <<pc, forks>>

Philosophers == 0..(N-1)

LeftFork(i) == i
RightFork(i) == (i + 1) % N

TypeOK ==
    /\ pc \in [Philosophers -> {"thinking", "hungry", "hasFirst", "eating"}]
    /\ forks \in [0..(N-1) -> 0..1]

Init ==
    /\ pc = [i \in Philosophers |-> "thinking"]
    /\ forks = [i \in 0..(N-1) |-> 1]

BecomeHungry(i) ==
    /\ pc[i] = "thinking"
    /\ pc' = [pc EXCEPT ![i] = "hungry"]
    /\ forks' = forks

AcquireFirstFork(i) ==
    /\ pc[i] = "hungry"
    /\ IF i = 0
       THEN /\ forks[LeftFork(i)] = 1
            /\ forks' = [forks EXCEPT ![LeftFork(i)] = 0]
       ELSE /\ forks[RightFork(i)] = 1
            /\ forks' = [forks EXCEPT ![RightFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "hasFirst"]

AcquireSecondFork(i) ==
    /\ pc[i] = "hasFirst"
    /\ IF i = 0
       THEN /\ forks[RightFork(i)] = 1
            /\ forks' = [forks EXCEPT ![RightFork(i)] = 0]
       ELSE /\ forks[LeftFork(i)] = 1
            /\ forks' = [forks EXCEPT ![LeftFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "eating"]

FinishEating(i) ==
    /\ pc[i] = "eating"
    /\ forks' = [forks EXCEPT ![LeftFork(i)] = 1, ![RightFork(i)] = 1]
    /\ pc' = [pc EXCEPT ![i] = "thinking"]

PhilosopherAction(i) ==
    \/ BecomeHungry(i)
    \/ AcquireFirstFork(i)
    \/ AcquireSecondFork(i)
    \/ FinishEating(i)

Next == \E i \in Philosophers : PhilosopherAction(i)

Fairness == \A i \in Philosophers : SF_vars(PhilosopherAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A i, j \in Philosophers :
        (i # j /\ (RightFork(i) = LeftFork(j) \/ LeftFork(i) = RightFork(j))) =>
        ~(pc[i] = "eating" /\ pc[j] = "eating")

Invariant == MutualExclusion

StarvationFreedom == \A i \in Philosophers : (pc[i] = "hungry") ~> (pc[i] = "eating")

===================================================================================