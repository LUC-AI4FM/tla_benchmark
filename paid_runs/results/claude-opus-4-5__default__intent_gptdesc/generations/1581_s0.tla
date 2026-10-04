-------------------------------- MODULE DiningPhilosophers --------------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS N

ASSUME N >= 2

Philosophers == 0..(N-1)
Forks == 0..(N-1)

LeftFork(p) == p
RightFork(p) == (p + 1) % N

LeftPhilosopher(f) == f
RightPhilosopher(f) == (f - 1 + N) % N

VARIABLES
    state,
    forkHolder

vars == <<state, forkHolder>>

PhilosopherStates == {"thinking", "hungry", "hasLeft", "hasRight", "eating"}

TypeOK ==
    /\ state \in [Philosophers -> PhilosopherStates]
    /\ forkHolder \in [Forks -> Philosophers \cup {-1}]

Init ==
    /\ state = [p \in Philosophers |-> "thinking"]
    /\ forkHolder = [f \in Forks |-> -1]

BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED forkHolder

PickUpLeftFork(p) ==
    /\ state[p] = "hungry"
    /\ forkHolder[LeftFork(p)] = -1
    /\ state' = [state EXCEPT ![p] = "hasLeft"]
    /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = p]

PickUpRightFork(p) ==
    /\ state[p] = "hungry"
    /\ forkHolder[RightFork(p)] = -1
    /\ state' = [state EXCEPT ![p] = "hasRight"]
    /\ forkHolder' = [forkHolder EXCEPT ![RightFork(p)] = p]

PickUpSecondForkAndEat(p) ==
    \/ /\ state[p] = "hasLeft"
       /\ forkHolder[RightFork(p)] = -1
       /\ state' = [state EXCEPT ![p] = "eating"]
       /\ forkHolder' = [forkHolder EXCEPT ![RightFork(p)] = p]
    \/ /\ state[p] = "hasRight"
       /\ forkHolder[LeftFork(p)] = -1
       /\ state' = [state EXCEPT ![p] = "eating"]
       /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = p]

PutDownAndRetry(p) ==
    \/ /\ state[p] = "hasLeft"
       /\ forkHolder[RightFork(p)] # -1
       /\ forkHolder[RightFork(p)] # p
       /\ state' = [state EXCEPT ![p] = "hungry"]
       /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = -1]
    \/ /\ state[p] = "hasRight"
       /\ forkHolder[LeftFork(p)] # -1
       /\ forkHolder[LeftFork(p)] # p
       /\ state' = [state EXCEPT ![p] = "hungry"]
       /\ forkHolder' = [forkHolder EXCEPT ![RightFork(p)] = -1]

FinishEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ forkHolder' = [forkHolder EXCEPT ![LeftFork(p)] = -1, ![RightFork(p)] = -1]

PhilosopherAction(p) ==
    \/ BecomeHungry(p)
    \/ PickUpLeftFork(p)
    \/ PickUpRightFork(p)
    \/ PickUpSecondForkAndEat(p)
    \/ PutDownAndRetry(p)
    \/ FinishEating(p)

Next == \E p \in Philosophers : PhilosopherAction(p)

Fairness ==
    /\ \A p \in Philosophers : WF_vars(BecomeHungry(p))
    /\ \A p \in Philosophers : WF_vars(PickUpLeftFork(p))
    /\ \A p \in Philosophers : WF_vars(PickUpRightFork(p))
    /\ \A p \in Philosophers : WF_vars(PickUpSecondForkAndEat(p))
    /\ \A p \in Philosophers : WF_vars(PutDownAndRetry(p))
    /\ \A p \in Philosophers : WF_vars(FinishEating(p))

Spec == Init /\ [][Next]_vars /\ Fairness

ForkMutualExclusion ==
    \A f \in Forks :
        forkHolder[f] = -1 
        \/ (forkHolder[f] \in Philosophers 
            /\ \A p \in Philosophers : 
                (p # forkHolder[f]) => 
                    ~(state[p] = "eating" /\ (LeftFork(p) = f \/ RightFork(p) = f)))

NoAdjacentEating ==
    \A p \in Philosophers :
        state[p] = "eating" => 
            /\ state[(p - 1 + N) % N] # "eating"
            /\ state[(p + 1) % N] # "eating"

ForkHeldByAtMostOne ==
    \A f \in Forks :
        Cardinality({p \in Philosophers : forkHolder[f] = p}) <= 1

EatingImpliesHoldsBothForks ==
    \A p \in Philosophers :
        state[p] = "eating" => 
            /\ forkHolder[LeftFork(p)] = p
            /\ forkHolder[RightFork(p)] = p

SafetyInvariant ==
    /\ TypeOK
    /\ ForkMutualExclusion
    /\ NoAdjacentEating
    /\ ForkHeldByAtMostOne
    /\ EatingImpliesHoldsBothForks

SomeoneCanAct ==
    \E p \in Philosophers :
        \/ state[p] = "thinking"
        \/ state[p] = "eating"
        \/ (state[p] = "hungry" /\ (forkHolder[LeftFork(p)] = -1 \/ forkHolder[RightFork(p)] = -1))
        \/ (state[p] = "hasLeft" /\ (forkHolder[RightFork(p)] = -1 \/ forkHolder[RightFork(p)] # p))
        \/ (state[p] = "hasRight" /\ (forkHolder[LeftFork(p)] = -1 \/ forkHolder[LeftFork(p)] # p))

DeadlockFreedom == [][SomeoneCanAct]_vars

StarvationFreedom ==
    \A p \in Philosophers : []<>(state[p] = "eating")

HungryEventuallyEats ==
    \A p \in Philosophers : 
        [](state[p] = "hungry" => <>(state[p] = "eating"))

Liveness ==
    /\ StarvationFreedom
    /\ HungryEventuallyEats

=============================================================================