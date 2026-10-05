-------------------------------- MODULE DiningPhilosophers --------------------------------
EXTENDS Integers, FiniteSets, Naturals

CONSTANTS N

ASSUME N >= 2

Philosophers == 0..(N-1)

LeftFork(p) == p
RightFork(p) == (p + 1) % N

LeftNeighbor(p) == (p - 1 + N) % N
RightNeighbor(p) == (p + 1) % N

Forks == 0..(N-1)

ForkOwners(f) == {f, (f - 1 + N) % N}

VARIABLES
    philState,
    forkHolder,
    forkClean,
    forkRequested

vars == <<philState, forkHolder, forkClean, forkRequested>>

TypeOK ==
    /\ philState \in [Philosophers -> {"thinking", "hungry", "eating"}]
    /\ forkHolder \in [Forks -> Philosophers]
    /\ \A f \in Forks : forkHolder[f] \in ForkOwners(f)
    /\ forkClean \in [Forks -> BOOLEAN]
    /\ forkRequested \in [Forks -> BOOLEAN]

Init ==
    /\ philState = [p \in Philosophers |-> "thinking"]
    /\ forkHolder \in {fh \in [Forks -> Philosophers] : \A f \in Forks : fh[f] \in ForkOwners(f)}
    /\ forkClean = [f \in Forks |-> FALSE]
    /\ forkRequested = [f \in Forks |-> FALSE]

HasFork(p, f) ==
    /\ f \in {LeftFork(p), RightFork(p)}
    /\ forkHolder[f] = p

HasBothForks(p) ==
    /\ HasFork(p, LeftFork(p))
    /\ HasFork(p, RightFork(p))

BecomeHungry(p) ==
    /\ philState[p] = "thinking"
    /\ philState' = [philState EXCEPT ![p] = "hungry"]
    /\ UNCHANGED <<forkHolder, forkClean, forkRequested>>

RequestFork(p, f) ==
    /\ philState[p] = "hungry"
    /\ f \in {LeftFork(p), RightFork(p)}
    /\ forkHolder[f] # p
    /\ forkRequested' = [forkRequested EXCEPT ![f] = TRUE]
    /\ UNCHANGED <<philState, forkHolder, forkClean>>

GiveFork(p, f) ==
    /\ f \in {LeftFork(p), RightFork(p)}
    /\ forkHolder[f] = p
    /\ forkRequested[f] = TRUE
    /\ \/ philState[p] = "thinking"
       \/ /\ philState[p] = "hungry"
          /\ forkClean[f] = FALSE
    /\ LET other == IF f = LeftFork(p) THEN LeftNeighbor(p) ELSE RightNeighbor(p)
       IN forkHolder' = [forkHolder EXCEPT ![f] = other]
    /\ forkClean' = [forkClean EXCEPT ![f] = TRUE]
    /\ forkRequested' = [forkRequested EXCEPT ![f] = FALSE]
    /\ UNCHANGED philState

StartEating(p) ==
    /\ philState[p] = "hungry"
    /\ HasBothForks(p)
    /\ philState' = [philState EXCEPT ![p] = "eating"]
    /\ forkClean' = [forkClean EXCEPT ![LeftFork(p)] = FALSE, ![RightFork(p)] = FALSE]
    /\ UNCHANGED <<forkHolder, forkRequested>>

StopEating(p) ==
    /\ philState[p] = "eating"
    /\ philState' = [philState EXCEPT ![p] = "thinking"]
    /\ UNCHANGED <<forkHolder, forkClean, forkRequested>>

PhilosopherAction(p) ==
    \/ BecomeHungry(p)
    \/ \E f \in {LeftFork(p), RightFork(p)} : RequestFork(p, f)
    \/ \E f \in {LeftFork(p), RightFork(p)} : GiveFork(p, f)
    \/ StartEating(p)
    \/ StopEating(p)

Next == \E p \in Philosophers : PhilosopherAction(p)

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
        ~(philState[p] = "eating" /\ philState[RightNeighbor(p)] = "eating")

ForkHeldByExactlyOneNeighbor ==
    \A f \in Forks : forkHolder[f] \in ForkOwners(f)

SafetyInvariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ ForkHeldByExactlyOneNeighbor

NoStarvation ==
    \A p \in Philosophers :
        (philState[p] = "hungry") ~> (philState[p] = "eating")

NoDeadlock ==
    []ENABLED(Next)

Progress ==
    []<><<Next>>_vars

=============================================================================