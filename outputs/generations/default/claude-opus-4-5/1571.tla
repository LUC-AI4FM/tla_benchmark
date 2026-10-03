---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N >= 2

Philosophers == 0..(N-1)

LeftFork(p) == p
RightFork(p) == (p + 1) % N

VARIABLES pc, forks

vars == <<pc, forks>>

TypeOK ==
    /\ pc \in [Philosophers -> {"thinking", "hungry", "waiting_second", "eating"}]
    /\ forks \in [0..(N-1) -> 0..1]

Init ==
    /\ pc = [p \in Philosophers |-> "thinking"]
    /\ forks = [f \in 0..(N-1) |-> 1]

\* Philosopher 0 acquires left fork first (opposite order)
AcquireFirstFork0 ==
    /\ pc[0] = "hungry"
    /\ forks[LeftFork(0)] = 1
    /\ forks' = [forks EXCEPT ![LeftFork(0)] = 0]
    /\ pc' = [pc EXCEPT ![0] = "waiting_second"]

AcquireSecondFork0 ==
    /\ pc[0] = "waiting_second"
    /\ forks[RightFork(0)] = 1
    /\ forks' = [forks EXCEPT ![RightFork(0)] = 0]
    /\ pc' = [pc EXCEPT ![0] = "eating"]

\* Philosophers 1 to N-1 acquire right fork first
AcquireFirstFork(p) ==
    /\ p \in 1..(N-1)
    /\ pc[p] = "hungry"
    /\ forks[RightFork(p)] = 1
    /\ forks' = [forks EXCEPT ![RightFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "waiting_second"]

AcquireSecondFork(p) ==
    /\ p \in 1..(N-1)
    /\ pc[p] = "waiting_second"
    /\ forks[LeftFork(p)] = 1
    /\ forks' = [forks EXCEPT ![LeftFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "eating"]

\* Common actions for all philosophers
StartThinking(p) ==
    /\ pc[p] = "thinking"
    /\ pc' = [pc EXCEPT ![p] = "hungry"]
    /\ UNCHANGED forks

FinishEating0 ==
    /\ pc[0] = "eating"
    /\ forks' = [forks EXCEPT ![LeftFork(0)] = 1, ![RightFork(0)] = 1]
    /\ pc' = [pc EXCEPT ![0] = "thinking"]

FinishEating(p) ==
    /\ p \in 1..(N-1)
    /\ pc[p] = "eating"
    /\ forks' = [forks EXCEPT ![LeftFork(p)] = 1, ![RightFork(p)] = 1]
    /\ pc' = [pc EXCEPT ![p] = "thinking"]

\* Actions for philosopher 0
Philosopher0Action ==
    \/ StartThinking(0)
    \/ AcquireFirstFork0
    \/ AcquireSecondFork0
    \/ FinishEating0

\* Actions for philosophers 1 to N-1
PhilosopherAction(p) ==
    \/ StartThinking(p)
    \/ AcquireFirstFork(p)
    \/ AcquireSecondFork(p)
    \/ FinishEating(p)

Next ==
    \/ Philosopher0Action
    \/ \E p \in 1..(N-1) : PhilosopherAction(p)

\* Strong fairness for each philosopher
Fairness ==
    /\ SF_vars(Philosopher0Action)
    /\ \A p \in 1..(N-1) : SF_vars(PhilosopherAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual exclusion - adjacent philosophers cannot eat simultaneously
MutualExclusion ==
    \A p \in Philosophers :
        ~(pc[p] = "eating" /\ pc[(p + 1) % N] = "eating")

\* Alternative formulation: No two philosophers sharing a fork can both be eating
ForkMutualExclusion ==
    \A f \in 0..(N-1) :
        LET leftPhil == f
            rightPhil == (f - 1 + N) % N
        IN ~(pc[leftPhil] = "eating" /\ pc[rightPhil] = "eating")

\* Liveness: Starvation freedom - every hungry philosopher eventually eats
StarvationFreedom ==
    \A p \in Philosophers : (pc[p] = "hungry") ~> (pc[p] = "eating")

\* Additional liveness: Every philosopher eventually eats
EventuallyEats ==
    \A p \in Philosophers : []<>(pc[p] = "eating")

=============================================================================