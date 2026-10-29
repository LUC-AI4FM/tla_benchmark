---- MODULE ChandyMisraDiningPhilosophers ----
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

VARIABLES state, forks

vars == << state, forks >>

Philosophers == 1..N
Forks == 1..N

\* Fork f lies between philosopher f and philosopher (f % N) + 1.
LeftFork(p)  == p
RightFork(p) == IF p = 1 THEN N ELSE p - 1
Endpoints(f) == {f, (f % N) + 1}

\* The other philosopher sharing fork f with philosopher p.
OtherEnd(f, p) == IF p = f THEN (f % N) + 1 ELSE f

AdjacentForks(p) == {LeftFork(p), RightFork(p)}

Neighbors(p, q) == p # q /\ \E f \in Forks : Endpoints(f) = {p, q}

States == {"thinking", "hungry", "eating"}

TypeOK ==
    /\ state \in [Philosophers -> States]
    /\ forks \in [Forks -> [holder : Philosophers, clean : BOOLEAN]]
    /\ \A f \in Forks : forks[f].holder \in Endpoints(f)

\* Every fork starts dirty, held by the lower-numbered of its two adjacent philosophers.
Init ==
    /\ state = [p \in Philosophers |-> "thinking"]
    /\ forks = [f \in Forks |->
                  [holder |-> IF f = N THEN 1 ELSE f,
                   clean  |-> FALSE]]

HoldsBothClean(p) ==
    \A f \in AdjacentForks(p) : forks[f].holder = p /\ forks[f].clean

BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED forks

Eat(p) ==
    /\ state[p] = "hungry"
    /\ HoldsBothClean(p)
    /\ state' = [state EXCEPT ![p] = "eating"]
    /\ UNCHANGED forks

\* After eating, both forks become dirty.
DoneEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ forks' = [f \in Forks |->
                   IF f \in AdjacentForks(p)
                   THEN [forks[f] EXCEPT !.clean = FALSE]
                   ELSE forks[f]]

\* A hungry neighbor implicitly requests the fork.
\* A non-eating holder of a dirty fork cleans it and hands it directly to that neighbor.
PassFork(p, f) ==
    /\ f \in AdjacentForks(p)
    /\ forks[f].holder = p
    /\ ~forks[f].clean
    /\ state[p] # "eating"
    /\ state[OtherEnd(f, p)] = "hungry"
    /\ forks' = [forks EXCEPT ![f] = [holder |-> OtherEnd(f, p), clean |-> TRUE]]
    /\ UNCHANGED state

Philosopher(p) ==
    \/ BecomeHungry(p)
    \/ Eat(p)
    \/ DoneEating(p)
    \/ \E f \in AdjacentForks(p) : PassFork(p, f)

Next == \E p \in Philosophers : Philosopher(p)

Fairness ==
    \A p \in Philosophers :
        /\ WF_vars(BecomeHungry(p))
        /\ WF_vars(Eat(p))
        /\ WF_vars(DoneEating(p))
        /\ \A f \in Forks : WF_vars(PassFork(p, f))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: no two philosophers sharing a fork eat simultaneously.
MutualExclusion ==
    \A p, q \in Philosophers :
        Neighbors(p, q) => ~(state[p] = "eating" /\ state[q] = "eating")

\* Liveness: no philosopher starves.
EveryHungryEventuallyEats ==
    \A p \in Philosophers : (state[p] = "hungry") ~> (state[p] = "eating")

NoStarvation ==
    \A p \in Philosophers : []<>(state[p] = "eating")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => (EveryHungryEventuallyEats /\ NoStarvation)
====