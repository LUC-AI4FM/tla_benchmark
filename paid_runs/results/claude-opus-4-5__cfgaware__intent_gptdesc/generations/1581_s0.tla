---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANT N

ASSUME N >= 2

VARIABLES
    philState,      \* philState[i] \in {"thinking", "hungry", "eating"}
    forkHolder      \* forkHolder[i] = philosopher holding fork i, or -1 if free

vars == <<philState, forkHolder>>

Philosophers == 0..(N-1)
Forks == 0..(N-1)

\* Fork i is the left fork of philosopher i
\* Fork (i+1) % N is the right fork of philosopher i
LeftFork(p) == p
RightFork(p) == (p + 1) % N

\* A philosopher's neighbors
LeftPhil(p) == (p - 1 + N) % N
RightPhil(p) == (p + 1) % N

TypeOK ==
    /\ philState \in [Philosophers -> {"thinking", "hungry", "eating"}]
    /\ forkHolder \in [Forks -> Philosophers \cup {-1}]

Init ==
    /\ philState = [p \in Philosophers |-> "thinking"]
    /\ forkHolder = [f \in Forks |-> -1]

\* A philosopher becomes hungry (wants to eat)
BecomeHungry(p) ==
    /\ philState[p] = "thinking"
    /\ philState' = [philState EXCEPT ![p] = "hungry"]
    /\ UNCHANGED forkHolder

\* A hungry philosopher picks up their left fork if available
PickupLeftFork(p) ==
    /\ philState[p] = "hungry"
    /\ forkHolder[LeftFork(p)] = -1
    /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = p]
    /\ UNCHANGED philState

\* A hungry philosopher picks up their right fork if available
PickupRightFork(p) ==
    /\ philState[p] = "hungry"
    /\ forkHolder[RightFork(p)] = -1
    /\ forkHolder' = [forkHolder EXCEPT ![RightFork(p)] = p]
    /\ UNCHANGED philState

\* A hungry philosopher who holds both forks starts eating
StartEating(p) ==
    /\ philState[p] = "hungry"
    /\ forkHolder[LeftFork(p)] = p
    /\ forkHolder[RightFork(p)] = p
    /\ philState' = [philState EXCEPT ![p] = "eating"]
    /\ UNCHANGED forkHolder

\* A philosopher finishes eating and returns to thinking
FinishEating(p) ==
    /\ philState[p] = "eating"
    /\ philState' = [philState EXCEPT ![p] = "thinking"]
    /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = -1, ![RightFork(p)] = -1]

\* A hungry philosopher may put down forks they hold (to avoid deadlock in some protocols)
PutDownForks(p) ==
    /\ philState[p] = "hungry"
    /\ \/ forkHolder[LeftFork(p)] = p
       \/ forkHolder[RightFork(p)] = p
    /\ forkHolder' = [f \in Forks |->
                        IF (f = LeftFork(p) \/ f = RightFork(p)) /\ forkHolder[f] = p
                        THEN -1
                        ELSE forkHolder[f]]
    /\ UNCHANGED philState

\* All possible actions for a philosopher
PhilAction(p) ==
    \/ BecomeHungry(p)
    \/ PickupLeftFork(p)
    \/ PickupRightFork(p)
    \/ StartEating(p)
    \/ FinishEating(p)
    \/ PutDownForks(p)

Next == \E p \in Philosophers : PhilAction(p)

\* Fairness: Weak fairness on all enabled actions for each philosopher
\* This ensures that if an action remains continuously enabled, it eventually happens
Fairness ==
    /\ \A p \in Philosophers : WF_vars(BecomeHungry(p))
    /\ \A p \in Philosophers : WF_vars(PickupLeftFork(p))
    /\ \A p \in Philosophers : WF_vars(PickupRightFork(p))
    /\ \A p \in Philosophers : WF_vars(StartEating(p))
    /\ \A p \in Philosophers : WF_vars(FinishEating(p))
    /\ \A p \in Philosophers : WF_vars(PutDownForks(p))

\* Strong fairness for fork acquisition to ensure starvation freedom
\* If a philosopher is hungry and their fork is infinitely often free, they eventually get it
StrongFairness ==
    /\ \A p \in Philosophers : SF_vars(PickupLeftFork(p))
    /\ \A p \in Philosophers : SF_vars(PickupRightFork(p))
    /\ \A p \in Philosophers : SF_vars(StartEating(p))

Spec == Init /\ [][Next]_vars /\ Fairness /\ StrongFairness

\* SAFETY PROPERTIES

\* No two adjacent philosophers eat simultaneously
NoAdjacentEating ==
    \A p \in Philosophers :
        ~(philState[p] = "eating" /\ philState[RightPhil(p)] = "eating")

\* A fork can only be held by at most one philosopher
ForkMutualExclusion ==
    \A f \in Forks :
        forkHolder[f] = -1 \/ 
        (forkHolder[f] \in Philosophers /\
         \A p \in Philosophers : (forkHolder[f] = p) => 
            ~\E q \in Philosophers : q # p /\ forkHolder[f] = q)

\* Only eating philosophers hold both their forks
ForkConsistency ==
    \A p \in Philosophers :
        philState[p] = "eating" => 
            (forkHolder[LeftFork(p)] = p /\ forkHolder[RightFork(p)] = p)

\* Combined invariant
Invariant ==
    /\ TypeOK
    /\ NoAdjacentEating
    /\ ForkMutualExclusion
    /\ ForkConsistency

\* LIVENESS PROPERTIES

\* Every philosopher eventually eats (starvation freedom)
\* For each philosopher, it is always the case that they will eventually eat
StarvationFree ==
    \A p \in Philosophers : []<>(philState[p] = "eating")

\* If a philosopher becomes hungry, they eventually eat
HungryEventuallyEats ==
    \A p \in Philosophers : 
        [](philState[p] = "hungry" => <>(philState[p] = "eating"))

\* Deadlock freedom is implied by the combination of:
\* 1. The invariant (safety)
\* 2. The fairness conditions
\* 3. The ability to put down forks
\* Under strong fairness, if any progress is possible, it will happen

=================================================================================