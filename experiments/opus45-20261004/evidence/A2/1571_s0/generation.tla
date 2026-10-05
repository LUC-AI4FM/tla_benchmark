---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 2

Philosophers == 0..(N-1)

VARIABLES sem, pc

vars == <<sem, pc>>

Left(i) == i
Right(i) == (i + 1) % N

TypeOK ==
    /\ sem \in [0..(N-1) -> {0, 1}]
    /\ pc \in [Philosophers -> {"l0", "l1", "l2", "l3", "l4", "l01", "l02", "l03", "l04"}]

Init ==
    /\ sem = [i \in 0..(N-1) |-> 1]
    /\ pc = [i \in Philosophers |-> IF i = 0 THEN "l01" ELSE "l1"]

\* Philosophers 1 through N-1: acquire right fork first, then left fork
\* l1: try to acquire right fork
\* l2: try to acquire left fork
\* l3: eating, then release right fork
\* l4: release left fork, go back to l1

AcquireRightFork(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "l1"
    /\ sem[Right(i)] = 1
    /\ sem' = [sem EXCEPT ![Right(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "l2"]

AcquireLeftFork(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "l2"
    /\ sem[Left(i)] = 1
    /\ sem' = [sem EXCEPT ![Left(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "l3"]

ReleaseRightFork(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "l3"
    /\ sem' = [sem EXCEPT ![Right(i)] = 1]
    /\ pc' = [pc EXCEPT ![i] = "l4"]

ReleaseLeftFork(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "l4"
    /\ sem' = [sem EXCEPT ![Left(i)] = 1]
    /\ pc' = [pc EXCEPT ![i] = "l1"]

\* Philosopher 0: acquire left fork first, then right fork (reversed order)
\* l01: try to acquire left fork
\* l02: try to acquire right fork
\* l03: eating, then release left fork
\* l04: release right fork, go back to l01

AcquireLeftForkP0 ==
    /\ pc[0] = "l01"
    /\ sem[Left(0)] = 1
    /\ sem' = [sem EXCEPT ![Left(0)] = 0]
    /\ pc' = [pc EXCEPT ![0] = "l02"]

AcquireRightForkP0 ==
    /\ pc[0] = "l02"
    /\ sem[Right(0)] = 1
    /\ sem' = [sem EXCEPT ![Right(0)] = 0]
    /\ pc' = [pc EXCEPT ![0] = "l03"]

ReleaseLeftForkP0 ==
    /\ pc[0] = "l03"
    /\ sem' = [sem EXCEPT ![Left(0)] = 1]
    /\ pc' = [pc EXCEPT ![0] = "l04"]

ReleaseRightForkP0 ==
    /\ pc[0] = "l04"
    /\ sem' = [sem EXCEPT ![Right(0)] = 1]
    /\ pc' = [pc EXCEPT ![0] = "l01"]

PhilosopherAction(i) ==
    IF i = 0
    THEN \/ AcquireLeftForkP0
         \/ AcquireRightForkP0
         \/ ReleaseLeftForkP0
         \/ ReleaseRightForkP0
    ELSE \/ AcquireRightFork(i)
         \/ AcquireLeftFork(i)
         \/ ReleaseRightFork(i)
         \/ ReleaseLeftFork(i)

Next == \E i \in Philosophers : PhilosopherAction(i)

\* Strong fairness for each philosopher
Fairness == \A i \in Philosophers : SF_vars(PhilosopherAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* A philosopher is eating if they are at l3 (for 1..N-1) or l03 (for philosopher 0)
IsEating(i) == IF i = 0 THEN pc[i] = "l03" ELSE pc[i] = "l3"

\* Safety: No two adjacent philosophers eat simultaneously
Invariant ==
    \A i \in Philosophers :
        ~(IsEating(i) /\ IsEating((i + 1) % N))

\* Liveness: Every philosopher eats infinitely often
StarvationFree ==
    \A i \in Philosophers : []<>IsEating(i)

=================================================================================