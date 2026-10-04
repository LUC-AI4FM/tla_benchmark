---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N

ASSUME N >= 2

Philosophers == 0..(N-1)

VARIABLES pc, sem

vars == <<pc, sem>>

\* Fork indices: philosopher i has fork i on their left and fork (i+1) % N on their right
LeftFork(i) == i
RightFork(i) == (i + 1) % N

\* Program counter states:
\* "thinking" - philosopher is thinking
\* "hungry" - philosopher wants to eat, hasn't picked up any fork
\* "hasFirst" - philosopher has picked up first fork, waiting for second
\* "eating" - philosopher has both forks and is eating

TypeOK ==
    /\ pc \in [Philosophers -> {"thinking", "hungry", "hasFirst", "eating"}]
    /\ sem \in [0..(N-1) -> {0, 1}]

Init ==
    /\ pc = [i \in Philosophers |-> "thinking"]
    /\ sem = [i \in 0..(N-1) |-> 1]

\* Philosopher becomes hungry
BecomeHungry(i) ==
    /\ pc[i] = "thinking"
    /\ pc' = [pc EXCEPT ![i] = "hungry"]
    /\ sem' = sem

\* First fork for philosopher 0 is left fork, for others it's right fork
FirstFork(i) == IF i = 0 THEN LeftFork(i) ELSE RightFork(i)
SecondFork(i) == IF i = 0 THEN RightFork(i) ELSE LeftFork(i)

\* Pick up first fork
PickUpFirst(i) ==
    /\ pc[i] = "hungry"
    /\ sem[FirstFork(i)] = 1
    /\ sem' = [sem EXCEPT ![FirstFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "hasFirst"]

\* Pick up second fork
PickUpSecond(i) ==
    /\ pc[i] = "hasFirst"
    /\ sem[SecondFork(i)] = 1
    /\ sem' = [sem EXCEPT ![SecondFork(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "eating"]

\* Put down both forks and return to thinking
FinishEating(i) ==
    /\ pc[i] = "eating"
    /\ sem' = [sem EXCEPT ![LeftFork(i)] = 1, ![RightFork(i)] = 1]
    /\ pc' = [pc EXCEPT ![i] = "thinking"]

\* All actions for philosopher i
PhilosopherAction(i) ==
    \/ BecomeHungry(i)
    \/ PickUpFirst(i)
    \/ PickUpSecond(i)
    \/ FinishEating(i)

Next == \E i \in Philosophers : PhilosopherAction(i)

\* Strong fairness for each philosopher's actions
Fairness == \A i \in Philosophers : SF_vars(PhilosopherAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Adjacent philosophers do not eat simultaneously
\* Two philosophers are adjacent if they share a fork
MutualExclusion ==
    \A i \in Philosophers :
        ~(pc[i] = "eating" /\ pc[(i + 1) % N] = "eating")

\* Liveness: Each philosopher eats infinitely often (starvation freedom)
StarvationFreedom == \A i \in Philosophers : []<>(pc[i] = "eating")

===================================================================================