---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N

ASSUME N >= 2

Philosophers == 0..(N-1)

ForkIds == 0..(N-1)

LeftFork(p) == p
RightFork(p) == (p + 1) % N

LeftNeighbor(p) == (p - 1 + N) % N
RightNeighbor(p) == (p + 1) % N

ForkOwners(f) == {f, (f - 1 + N) % N}

VARIABLES
    state,
    forkHolder,
    forkState,
    forkRequested

vars == <<state, forkHolder, forkState, forkRequested>>

PhilosopherStates == {"thinking", "hungry", "eating"}
ForkStates == {"clean", "dirty"}

TypeInvariant ==
    /\ state \in [Philosophers -> PhilosopherStates]
    /\ forkHolder \in [ForkIds -> Philosophers]
    /\ \A f \in ForkIds : forkHolder[f] \in ForkOwners(f)
    /\ forkState \in [ForkIds -> ForkStates]
    /\ forkRequested \in [ForkIds -> BOOLEAN]

Init ==
    /\ state = [p \in Philosophers |-> "thinking"]
    /\ forkHolder = [f \in ForkIds |-> f]
    /\ forkState = [f \in ForkIds |-> "dirty"]
    /\ forkRequested = [f \in ForkIds |-> FALSE]

HasFork(p, f) ==
    forkHolder[f] = p

HasBothForks(p) ==
    /\ HasFork(p, LeftFork(p))
    /\ HasFork(p, RightFork(p))

CanEat(p) ==
    /\ state[p] = "hungry"
    /\ HasBothForks(p)

BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED <<forkHolder, forkState, forkRequested>>

RequestFork(p, f) ==
    /\ state[p] = "hungry"
    /\ f \in {LeftFork(p), RightFork(p)}
    /\ ~HasFork(p, f)
    /\ ~forkRequested[f]
    /\ forkRequested' = [forkRequested EXCEPT ![f] = TRUE]
    /\ UNCHANGED <<state, forkHolder, forkState>>

GiveFork(p, f) ==
    /\ f \in {LeftFork(p), RightFork(p)}
    /\ HasFork(p, f)
    /\ forkRequested[f]
    /\ state[p] /= "eating"
    /\ forkState[f] = "dirty"
    LET other == IF f = LeftFork(p) THEN LeftNeighbor(p) ELSE RightNeighbor(p)
    IN
        /\ forkHolder' = [forkHolder EXCEPT ![f] = other]
        /\ forkState' = [forkState EXCEPT ![f] = "clean"]
        /\ forkRequested' = [forkRequested EXCEPT ![f] = FALSE]
        /\ UNCHANGED <<state>>

StartEating(p) ==
    /\ CanEat(p)
    /\ state' = [state EXCEPT ![p] = "eating"]
    /\ UNCHANGED <<forkHolder, forkState, forkRequested>>

StopEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ forkState' = [forkState EXCEPT 
                        ![LeftFork(p)] = "dirty",
                        ![RightFork(p)] = "dirty"]
    /\ UNCHANGED <<forkHolder, forkRequested>>

PhilosopherAction(p) ==
    \/ BecomeHungry(p)
    \/ \E f \in {LeftFork(p), RightFork(p)} : RequestFork(p, f)
    \/ \E f \in {LeftFork(p), RightFork(p)} : GiveFork(p, f)
    \/ StartEating(p)
    \/ StopEating(p)

Next ==
    \E p \in Philosophers : PhilosopherAction(p)

Fairness ==
    \A p \in Philosophers :
        /\ WF_vars(BecomeHungry(p))
        /\ WF_vars(StartEating(p))
        /\ WF_vars(StopEating(p))
        /\ \A f \in {LeftFork(p), RightFork(p)} :
            /\ WF_vars(RequestFork(p, f))
            /\ WF_vars(GiveFork(p, f))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A p \in Philosophers :
        ~(state[p] = "eating" /\ state[RightNeighbor(p)] = "eating")

ForkExclusivity ==
    \A f \in ForkIds :
        \E! p \in ForkOwners(f) : forkHolder[f] = p

Safety == []MutualExclusion

Invariants == [](TypeInvariant /\ ForkExclusivity)

NoStarvation ==
    \A p \in Philosophers :
        (state[p] = "hungry") ~> (state[p] = "eating")

Liveness == NoStarvation

NoDeadlock == []ENABLED(Next)

Progress == NoDeadlock

=============================================================================