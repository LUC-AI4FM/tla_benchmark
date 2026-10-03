---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES pc, sem

vars == <<pc, sem>>

Philosophers == 0..(N-1)

\* Each philosopher can be in one of these states:
\* "thinking" - initial state
\* "hungry" - wants to eat, trying to acquire forks
\* "hasFirst" - has acquired first fork, waiting for second
\* "eating" - has both forks, eating
\* "releasing" - releasing forks after eating

\* Fork indices: fork i is between philosopher i and philosopher (i+1) mod N
\* Philosopher i's left fork is fork i
\* Philosopher i's right fork is fork (i-1+N) mod N

LeftFork(i) == i
RightFork(i) == (i - 1 + N) % N

\* For asymmetric solution:
\* Philosopher 0: picks up left fork first, then right fork
\* Philosophers 1 to N-1: pick up right fork first, then left fork

FirstFork(i) == IF i = 0 THEN LeftFork(i) ELSE RightFork(i)
SecondFork(i) == IF i = 0 THEN RightFork(i) ELSE LeftFork(i)

TypeOK == 
    /\ pc \in [Philosophers -> {"thinking", "hungry", "hasFirst", "eating", "releasing"}]
    /\ sem \in [0..(N-1) -> {0, 1}]

Init ==
    /\ pc = [i \in Philosophers |-> "thinking"]
    /\ sem = [i \in 0..(N-1) |-> 1]  \* All forks available (semaphore = 1)

\* Philosopher i becomes hungry
BecomeHungry(i) ==
    /\ pc[i] = "thinking"
    /\ pc' = [pc EXCEPT ![i] = "hungry"]
    /\ UNCHANGED sem

\* Philosopher i acquires first fork
AcquireFirst(i) ==
    /\ pc[i] = "hungry"
    /\ sem[FirstFork(i)] = 1
    /\ sem' = [sem EXCEPT ![FirstFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "hasFirst"]

\* Philosopher i acquires second fork and starts eating
AcquireSecond(i) ==
    /\ pc[i] = "hasFirst"
    /\ sem[SecondFork(i)] = 1
    /\ sem' = [sem EXCEPT ![SecondFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "eating"]

\* Philosopher i finishes eating and starts releasing
FinishEating(i) ==
    /\ pc[i] = "eating"
    /\ pc' = [pc EXCEPT ![i] = "releasing"]
    /\ UNCHANGED sem

\* Philosopher i releases both forks and goes back to thinking
ReleaseForks(i) ==
    /\ pc[i] = "releasing"
    /\ sem' = [sem EXCEPT ![FirstFork(i)] = 1, ![SecondFork(i)] = 1]
    /\ pc' = [pc EXCEPT ![i] = "thinking"]

\* All actions for philosopher i
PhilosopherAction(i) ==
    \/ BecomeHungry(i)
    \/ AcquireFirst(i)
    \/ AcquireSecond(i)
    \/ FinishEating(i)
    \/ ReleaseForks(i)

Next == \E i \in Philosophers : PhilosopherAction(i)

\* Strong fairness for each philosopher's actions
Fairness == \A i \in Philosophers : SF_vars(PhilosopherAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety invariant: adjacent philosophers do not eat simultaneously
\* Philosophers i and (i+1) mod N are adjacent
Invariant == \A i \in Philosophers : 
    ~(pc[i] = "eating" /\ pc[(i + 1) % N] = "eating")

\* Starvation freedom: each philosopher eats infinitely often
StarvationFree == \A i \in Philosophers : []<>(pc[i] = "eating")

=============================================================================