---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 1

Philosophers == 0..(N-1)
Forks == 0..(N-1)

LeftFork(p) == p
RightFork(p) == (p + 1) % N

LeftNeighbor(p) == (p - 1 + N) % N
RightNeighbor(p) == (p + 1) % N

VARIABLES state, forkHolder

vars == <<state, forkHolder>>

TypeOK ==
    /\ state \in [Philosophers -> {"thinking", "hungry", "hasLeft", "eating"}]
    /\ forkHolder \in [Forks -> Philosophers \cup {-1}]

Init ==
    /\ state = [p \in Philosophers |-> "thinking"]
    /\ forkHolder = [f \in Forks |-> -1]

BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED forkHolder

AcquireLeftFork(p) ==
    /\ state[p] = "hungry"
    /\ forkHolder[LeftFork(p)] = -1
    /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = p]
    /\ state' = [state EXCEPT ![p] = "hasLeft"]

AcquireRightForkAndEat(p) ==
    /\ state[p] = "hasLeft"
    /\ forkHolder[RightFork(p)] = -1
    /\ forkHolder' = [forkHolder EXCEPT ![RightFork(p)] = p]
    /\ state' = [state EXCEPT ![p] = "eating"]

ReleaseLeftForkWhenWaiting(p) ==
    /\ state[p] = "hasLeft"
    /\ forkHolder[RightFork(p)] # -1
    /\ forkHolder[RightFork(p)] # p
    /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = -1]
    /\ state' = [state EXCEPT ![p] = "hungry"]

FinishEating(p) ==
    /\ state[p] = "eating"
    /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = -1, ![RightFork(p)] = -1]
    /\ state' = [state EXCEPT ![p] = "thinking"]

Next ==
    \E p \in Philosophers :
        \/ BecomeHungry(p)
        \/ AcquireLeftFork(p)
        \/ AcquireRightForkAndEat(p)
        \/ ReleaseLeftForkWhenWaiting(p)
        \/ FinishEating(p)

Fairness ==
    /\ \A p \in Philosophers : WF_vars(BecomeHungry(p))
    /\ \A p \in Philosophers : WF_vars(AcquireLeftFork(p))
    /\ \A p \in Philosophers : WF_vars(AcquireRightForkAndEat(p))
    /\ \A p \in Philosophers : WF_vars(ReleaseLeftForkWhenWaiting(p))
    /\ \A p \in Philosophers : WF_vars(FinishEating(p))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A p \in Philosophers :
        state[p] = "eating" => state[LeftNeighbor(p)] # "eating" /\ state[RightNeighbor(p)] # "eating"

ForkIntegrity ==
    \A f \in Forks :
        forkHolder[f] \in Philosophers \cup {-1}

ForkExclusivity ==
    \A f \in Forks :
        \A p1, p2 \in Philosophers :
            (forkHolder[f] = p1 /\ forkHolder[f] = p2) => p1 = p2

ForkHeldOnlyByAdjacent ==
    \A f \in Forks :
        forkHolder[f] # -1 =>
            (forkHolder[f] = f \/ forkHolder[f] = (f - 1 + N) % N)

EatingImpliesHoldsBothForks ==
    \A p \in Philosophers :
        state[p] = "eating" =>
            /\ forkHolder[LeftFork(p)] = p
            /\ forkHolder[RightFork(p)] = p

HasLeftImpliesHoldsLeftFork ==
    \A p \in Philosophers :
        state[p] = "hasLeft" => forkHolder[LeftFork(p)] = p

ThinkingImpliesNoForks ==
    \A p \in Philosophers :
        state[p] = "thinking" =>
            /\ forkHolder[LeftFork(p)] # p
            /\ forkHolder[RightFork(p)] # p

Invariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ ForkIntegrity
    /\ ForkExclusivity
    /\ ForkHeldOnlyByAdjacent
    /\ EatingImpliesHoldsBothForks
    /\ HasLeftImpliesHoldsLeftFork

NoDeadlock ==
    []<><<Next>>_vars

StarvationFreedom ==
    \A p \in Philosophers : []<>(state[p] = "eating")

EventuallyEats ==
    \A p \in Philosophers : [](state[p] = "hungry" => <>(state[p] = "eating"))

===================================================================================