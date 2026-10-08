-------------------------------- MODULE DiningPhilosophers --------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 1

Philosophers == 0..(N-1)
Forks == 0..(N-1)

LeftFork(p) == p
RightFork(p) == (p + 1) % N

LeftPhilosopher(f) == f
RightPhilosopher(f) == (f - 1 + N) % N

VARIABLES
    philState,
    forkHolder

vars == <<philState, forkHolder>>

TypeOK ==
    /\ philState \in [Philosophers -> {"thinking", "hungry", "hasLeft", "hasRight", "eating"}]
    /\ forkHolder \in [Forks -> Philosophers \cup {-1}]

Init ==
    /\ philState = [p \in Philosophers |-> "thinking"]
    /\ forkHolder = [f \in Forks |-> -1]

BecomeHungry(p) ==
    /\ philState[p] = "thinking"
    /\ philState' = [philState EXCEPT ![p] = "hungry"]
    /\ UNCHANGED forkHolder

AcquireLeftFork(p) ==
    /\ philState[p] = "hungry"
    /\ forkHolder[LeftFork(p)] = -1
    /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = p]
    /\ philState' = [philState EXCEPT ![p] = "hasLeft"]

AcquireRightFork(p) ==
    /\ philState[p] = "hungry"
    /\ forkHolder[RightFork(p)] = -1
    /\ forkHolder' = [forkHolder EXCEPT ![RightFork(p)] = p]
    /\ philState' = [philState EXCEPT ![p] = "hasRight"]

AcquireSecondForkFromLeft(p) ==
    /\ philState[p] = "hasLeft"
    /\ forkHolder[RightFork(p)] = -1
    /\ forkHolder' = [forkHolder EXCEPT ![RightFork(p)] = p]
    /\ philState' = [philState EXCEPT ![p] = "eating"]

AcquireSecondForkFromRight(p) ==
    /\ philState[p] = "hasRight"
    /\ forkHolder[LeftFork(p)] = -1
    /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = p]
    /\ philState' = [philState EXCEPT ![p] = "eating"]

ReleaseLeftForkWhenBlocked(p) ==
    /\ philState[p] = "hasLeft"
    /\ forkHolder[RightFork(p)] # -1
    /\ forkHolder[RightFork(p)] # p
    /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = -1]
    /\ philState' = [philState EXCEPT ![p] = "hungry"]

ReleaseRightForkWhenBlocked(p) ==
    /\ philState[p] = "hasRight"
    /\ forkHolder[LeftFork(p)] # -1
    /\ forkHolder[LeftFork(p)] # p
    /\ forkHolder' = [forkHolder EXCEPT ![RightFork(p)] = -1]
    /\ philState' = [philState EXCEPT ![p] = "hungry"]

FinishEating(p) ==
    /\ philState[p] = "eating"
    /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = -1, ![RightFork(p)] = -1]
    /\ philState' = [philState EXCEPT ![p] = "thinking"]

PhilosopherAction(p) ==
    \/ BecomeHungry(p)
    \/ AcquireLeftFork(p)
    \/ AcquireRightFork(p)
    \/ AcquireSecondForkFromLeft(p)
    \/ AcquireSecondForkFromRight(p)
    \/ ReleaseLeftForkWhenBlocked(p)
    \/ ReleaseRightForkWhenBlocked(p)
    \/ FinishEating(p)

Next == \E p \in Philosophers : PhilosopherAction(p)

Fairness ==
    /\ \A p \in Philosophers : WF_vars(BecomeHungry(p))
    /\ \A p \in Philosophers : WF_vars(AcquireLeftFork(p))
    /\ \A p \in Philosophers : WF_vars(AcquireRightFork(p))
    /\ \A p \in Philosophers : WF_vars(AcquireSecondForkFromLeft(p))
    /\ \A p \in Philosophers : WF_vars(AcquireSecondForkFromRight(p))
    /\ \A p \in Philosophers : WF_vars(ReleaseLeftForkWhenBlocked(p))
    /\ \A p \in Philosophers : WF_vars(ReleaseRightForkWhenBlocked(p))
    /\ \A p \in Philosophers : WF_vars(FinishEating(p))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A p \in Philosophers :
        ~(philState[p] = "eating" /\ philState[(p + 1) % N] = "eating")

ForkIntegrity ==
    \A f \in Forks :
        forkHolder[f] \in Philosophers \cup {-1}

ForkExclusivity ==
    \A f \in Forks :
        \A p1, p2 \in Philosophers :
            (forkHolder[f] = p1 /\ forkHolder[f] = p2) => p1 = p2

EatingImpliesHoldingBothForks ==
    \A p \in Philosophers :
        philState[p] = "eating" =>
            /\ forkHolder[LeftFork(p)] = p
            /\ forkHolder[RightFork(p)] = p

ForkHeldImpliesProperState ==
    \A f \in Forks :
        forkHolder[f] # -1 =>
            LET p == forkHolder[f]
            IN \/ (f = LeftFork(p) /\ philState[p] \in {"hasLeft", "eating"})
               \/ (f = RightFork(p) /\ philState[p] \in {"hasRight", "eating"})

ResourceIntegrity ==
    /\ ForkIntegrity
    /\ ForkExclusivity
    /\ EatingImpliesHoldingBothForks
    /\ ForkHeldImpliesProperState

Safety ==
    /\ TypeOK
    /\ MutualExclusion
    /\ ResourceIntegrity

SomeoneCanAct ==
    \E p \in Philosophers : 
        \/ philState[p] = "thinking"
        \/ philState[p] = "eating"
        \/ (philState[p] = "hungry" /\ (forkHolder[LeftFork(p)] = -1 \/ forkHolder[RightFork(p)] = -1))
        \/ (philState[p] = "hasLeft" /\ (forkHolder[RightFork(p)] = -1 \/ forkHolder[RightFork(p)] # p))
        \/ (philState[p] = "hasRight" /\ (forkHolder[LeftFork(p)] = -1 \/ forkHolder[LeftFork(p)] # p))

DeadlockFreedom == [][SomeoneCanAct]_vars

StarvationFreedom ==
    \A p \in Philosophers : []<>(philState[p] = "eating")

EventuallyEats(p) == <>(philState[p] = "eating")

AlwaysEventuallyEats(p) == [](philState[p] = "hungry" => EventuallyEats(p))

Liveness ==
    /\ StarvationFreedom
    /\ \A p \in Philosophers : AlwaysEventuallyEats(p)

=============================================================================