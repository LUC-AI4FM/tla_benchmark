---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N

ASSUME N > 1

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

\* Philosopher 0 acquires left fork first (opposite order to break symmetry)
\* Philosophers 1 to N-1 acquire right fork first

FirstFork(i) == IF i = 0 THEN LeftFork(i) ELSE RightFork(i)
SecondFork(i) == IF i = 0 THEN RightFork(i) ELSE LeftFork(i)

BecomeHungry(i) ==
    /\ pc[i] = "thinking"
    /\ pc' = [pc EXCEPT ![i] = "hungry"]
    /\ forks' = forks

AcquireFirstFork(i) ==
    /\ pc[i] = "hungry"
    /\ forks[FirstFork(i)] = 1
    /\ forks' = [forks EXCEPT ![FirstFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "hasFirst"]

AcquireSecondFork(i) ==
    /\ pc[i] = "hasFirst"
    /\ forks[SecondFork(i)] = 1
    /\ forks' = [forks EXCEPT ![SecondFork(i)] = 0]
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

\* Strong fairness for each philosopher's actions
Fairness == \A i \in Philosophers : SF_vars(PhilosopherAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual exclusion - no two adjacent philosophers can eat simultaneously
MutualExclusion ==
    \A i \in Philosophers :
        ~(pc[i] = "eating" /\ pc[(i + 1) % N] = "eating")

\* Alternative formulation: At most one philosopher holds each fork
ForkMutualExclusion ==
    \A f \in 0..(N-1) :
        LET holders == {i \in Philosophers : 
            (pc[i] \in {"hasFirst", "eating"} /\ FirstFork(i) = f) \/
            (pc[i] = "eating" /\ SecondFork(i) = f)}
        IN Cardinality(holders) <= 1

\* Liveness: Starvation freedom - every hungry philosopher eventually eats
StarvationFreedom == \A i \in Philosophers : 
    (pc[i] = "hungry" \/ pc[i] = "hasFirst") ~> pc[i] = "eating"

\* Every philosopher can eventually eat
EventuallyEats == \A i \in Philosophers : []<>(pc[i] = "eating")

===============================================================================