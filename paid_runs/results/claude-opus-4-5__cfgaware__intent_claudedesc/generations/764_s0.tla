---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, Naturals, FiniteSets, Sequences

CONSTANT N

ASSUME N >= 2

Philosophers == 0..(N-1)

LeftFork(p) == p
RightFork(p) == (p + 1) % N

LeftNeighbor(p) == (p - 1 + N) % N
RightNeighbor(p) == (p + 1) % N

ForkOwner(f) == f
ForkSharer(f) == (f - 1 + N) % N

VARIABLES
    state,
    forkOwner,
    forkClean,
    forkRequested

vars == <<state, forkOwner, forkClean, forkRequested>>

TypeOK ==
    /\ state \in [Philosophers -> {"thinking", "hungry", "eating"}]
    /\ forkOwner \in [Philosophers -> Philosophers]
    /\ forkClean \in [Philosophers -> BOOLEAN]
    /\ forkRequested \in [Philosophers -> [Philosophers -> BOOLEAN]]
    /\ \A f \in Philosophers : forkOwner[f] \in {ForkOwner(f), ForkSharer(f)}

MutualExclusion ==
    \A p1, p2 \in Philosophers :
        (p1 # p2 /\ (LeftFork(p1) = LeftFork(p2) \/ LeftFork(p1) = RightFork(p2) \/
                     RightFork(p1) = LeftFork(p2) \/ RightFork(p1) = RightFork(p2)))
        => ~(state[p1] = "eating" /\ state[p2] = "eating")

Init ==
    /\ state = [p \in Philosophers |-> "thinking"]
    /\ forkOwner = [f \in Philosophers |-> ForkOwner(f)]
    /\ forkClean = [f \in Philosophers |-> FALSE]
    /\ forkRequested = [p \in Philosophers |-> [q \in Philosophers |-> FALSE]]

HasLeftFork(p) == forkOwner[LeftFork(p)] = p
HasRightFork(p) == forkOwner[RightFork(p)] = p
HasBothForks(p) == HasLeftFork(p) /\ HasRightFork(p)

BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ LET leftNeighbor == LeftNeighbor(p)
           rightNeighbor == RightNeighbor(p)
       IN forkRequested' = [forkRequested EXCEPT 
            ![p][leftNeighbor] = IF ~HasLeftFork(p) THEN TRUE ELSE forkRequested[p][leftNeighbor],
            ![p][rightNeighbor] = IF ~HasRightFork(p) THEN TRUE ELSE forkRequested[p][rightNeighbor]]
    /\ UNCHANGED <<forkOwner, forkClean>>

SendForkLeft(p) ==
    /\ state[p] # "eating"
    /\ HasLeftFork(p)
    /\ forkRequested[LeftNeighbor(p)][p] = TRUE
    /\ forkClean[LeftFork(p)] = FALSE
    /\ forkOwner' = [forkOwner EXCEPT ![LeftFork(p)] = LeftNeighbor(p)]
    /\ forkClean' = [forkClean EXCEPT ![LeftFork(p)] = TRUE]
    /\ forkRequested' = [forkRequested EXCEPT 
        ![LeftNeighbor(p)][p] = FALSE,
        ![p][LeftNeighbor(p)] = IF state[p] = "hungry" THEN TRUE ELSE forkRequested[p][LeftNeighbor(p)]]
    /\ UNCHANGED state

SendForkRight(p) ==
    /\ state[p] # "eating"
    /\ HasRightFork(p)
    /\ forkRequested[RightNeighbor(p)][p] = TRUE
    /\ forkClean[RightFork(p)] = FALSE
    /\ forkOwner' = [forkOwner EXCEPT ![RightFork(p)] = RightNeighbor(p)]
    /\ forkClean' = [forkClean EXCEPT ![RightFork(p)] = TRUE]
    /\ forkRequested' = [forkRequested EXCEPT 
        ![RightNeighbor(p)][p] = FALSE,
        ![p][RightNeighbor(p)] = IF state[p] = "hungry" THEN TRUE ELSE forkRequested[p][RightNeighbor(p)]]
    /\ UNCHANGED state

StartEating(p) ==
    /\ state[p] = "hungry"
    /\ HasBothForks(p)
    /\ state' = [state EXCEPT ![p] = "eating"]
    /\ UNCHANGED <<forkOwner, forkClean, forkRequested>>

StopEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ forkClean' = [forkClean EXCEPT 
        ![LeftFork(p)] = FALSE,
        ![RightFork(p)] = FALSE]
    /\ UNCHANGED <<forkOwner, forkRequested>>

Next ==
    \E p \in Philosophers :
        \/ BecomeHungry(p)
        \/ SendForkLeft(p)
        \/ SendForkRight(p)
        \/ StartEating(p)
        \/ StopEating(p)

Fairness ==
    \A p \in Philosophers :
        /\ WF_vars(BecomeHungry(p))
        /\ WF_vars(SendForkLeft(p))
        /\ WF_vars(SendForkRight(p))
        /\ WF_vars(StartEating(p))
        /\ WF_vars(StopEating(p))

Spec == Init /\ [][Next]_vars /\ Fairness

NoStarvation == \A p \in Philosophers : state[p] = "hungry" ~> state[p] = "eating"

Liveness == \A p \in Philosophers : []<>(state[p] = "eating")

=============================================================================