---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N

ASSUME N >= 2

Philosophers == 0..(N-1)

VARIABLES pc, sem

vars == <<pc, sem>>

\* Each philosopher has states: "thinking", "hungry", "hasFirst", "eating"
\* For philosophers 1..N-1: right fork first, then left
\* For philosopher 0: left fork first, then right

\* Fork i is between philosopher i and philosopher (i+1) mod N
\* Philosopher i's right fork is fork i
\* Philosopher i's left fork is fork (i-1+N) mod N

RightFork(i) == i
LeftFork(i) == (i - 1 + N) % N

TypeOK == /\ pc \in [Philosophers -> {"thinking", "hungry", "hasFirst", "eating"}]
          /\ sem \in [0..(N-1) -> {0, 1}]

Init == /\ pc = [i \in Philosophers |-> "thinking"]
        /\ sem = [i \in 0..(N-1) |-> 1]

\* Philosopher becomes hungry
BecomeHungry(i) ==
    /\ pc[i] = "thinking"
    /\ pc' = [pc EXCEPT ![i] = "hungry"]
    /\ sem' = sem

\* Philosopher 0 picks up left fork first
AcquireFirstFork0 ==
    /\ pc[0] = "hungry"
    /\ sem[LeftFork(0)] = 1
    /\ sem' = [sem EXCEPT ![LeftFork(0)] = 0]
    /\ pc' = [pc EXCEPT ![0] = "hasFirst"]

\* Philosopher 0 picks up right fork second
AcquireSecondFork0 ==
    /\ pc[0] = "hasFirst"
    /\ sem[RightFork(0)] = 1
    /\ sem' = [sem EXCEPT ![RightFork(0)] = 0]
    /\ pc' = [pc EXCEPT ![0] = "eating"]

\* Philosophers 1..N-1 pick up right fork first
AcquireFirstForkOther(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "hungry"
    /\ sem[RightFork(i)] = 1
    /\ sem' = [sem EXCEPT ![RightFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "hasFirst"]

\* Philosophers 1..N-1 pick up left fork second
AcquireSecondForkOther(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "hasFirst"
    /\ sem[LeftFork(i)] = 1
    /\ sem' = [sem EXCEPT ![LeftFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "eating"]

\* Philosopher finishes eating and releases both forks
FinishEating(i) ==
    /\ pc[i] = "eating"
    /\ pc' = [pc EXCEPT ![i] = "thinking"]
    /\ sem' = [sem EXCEPT ![RightFork(i)] = 1, ![LeftFork(i)] = 1]

\* Actions for philosopher 0
Phil0Action ==
    \/ AcquireFirstFork0
    \/ AcquireSecondFork0
    \/ BecomeHungry(0)
    \/ FinishEating(0)

\* Actions for philosophers 1..N-1
PhilOtherAction(i) ==
    \/ AcquireFirstForkOther(i)
    \/ AcquireSecondForkOther(i)
    \/ BecomeHungry(i)
    \/ FinishEating(i)

\* All actions for philosopher i
PhilAction(i) ==
    IF i = 0 
    THEN Phil0Action
    ELSE PhilOtherAction(i)

Next == \E i \in Philosophers : PhilAction(i)

\* Strong fairness for each philosopher's actions
Fairness == \A i \in Philosophers : SF_vars(PhilAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Adjacent philosophers do not eat simultaneously
\* Philosopher i and philosopher (i+1) mod N are adjacent
MutualExclusion == 
    \A i \in Philosophers : 
        ~(pc[i] = "eating" /\ pc[(i + 1) % N] = "eating")

\* Liveness: Each philosopher eats infinitely often (starvation freedom)
StarvationFreedom == 
    \A i \in Philosophers : []<>(pc[i] = "eating")

===================================================================================