---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 2

Philosophers == 0..(N-1)

LeftFork(p) == p
RightFork(p) == (p + 1) % N

VARIABLES
    forks,
    state,
    pc

vars == <<forks, state, pc>>

TypeOK ==
    /\ forks \in [0..(N-1) -> 0..1]
    /\ state \in [Philosophers -> {"thinking", "eating"}]
    /\ pc \in [Philosophers -> {"think", "acq1", "acq2", "eat", "rel"}]

Init ==
    /\ forks = [f \in 0..(N-1) |-> 1]
    /\ state = [p \in Philosophers |-> "thinking"]
    /\ pc = [p \in Philosophers |-> "think"]

FirstFork(p) == IF p = 0 THEN LeftFork(p) ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

Think(p) ==
    /\ pc[p] = "think"
    /\ pc' = [pc EXCEPT ![p] = "acq1"]
    /\ UNCHANGED <<forks, state>>

AcquireFirst(p) ==
    /\ pc[p] = "acq1"
    /\ forks[FirstFork(p)] = 1
    /\ forks' = [forks EXCEPT ![FirstFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "acq2"]
    /\ UNCHANGED state

AcquireSecond(p) ==
    /\ pc[p] = "acq2"
    /\ forks[SecondFork(p)] = 1
    /\ forks' = [forks EXCEPT ![SecondFork(p)] = 0]
    /\ pc' = [pc EXCEPT ![p] = "eat"]
    /\ state' = [state EXCEPT ![p] = "eating"]

Eat(p) ==
    /\ pc[p] = "eat"
    /\ pc' = [pc EXCEPT ![p] = "rel"]
    /\ UNCHANGED <<forks, state>>

Release(p) ==
    /\ pc[p] = "rel"
    /\ forks' = [forks EXCEPT ![LeftFork(p)] = 1, ![RightFork(p)] = 1]
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ pc' = [pc EXCEPT ![p] = "think"]

PhilosopherAction(p) ==
    \/ Think(p)
    \/ AcquireFirst(p)
    \/ AcquireSecond(p)
    \/ Eat(p)
    \/ Release(p)

Next == \E p \in Philosophers : PhilosopherAction(p)

Fairness ==
    \A p \in Philosophers :
        /\ SF_vars(Think(p))
        /\ SF_vars(AcquireFirst(p))
        /\ SF_vars(AcquireSecond(p))
        /\ SF_vars(Eat(p))
        /\ SF_vars(Release(p))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A p \in Philosophers :
        state[p] = "eating" => state[(p + 1) % N] /= "eating"

Invariant == MutualExclusion

StarvationFreedom ==
    \A p \in Philosophers : []<>(state[p] = "eating")

=============================================================================