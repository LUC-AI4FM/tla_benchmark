---------------------------- MODULE DiningPhilosophersChandyMisra ----------------------------

EXTENDS Integers, FiniteSets, Naturals

CONSTANTS N

ASSUME N >= 2

Philosophers == 0 .. (N - 1)

\* Fork i is shared between philosopher i and philosopher (i + 1) % N
Forks == 0 .. (N - 1)

\* Left fork of philosopher p is fork (p - 1 + N) % N
\* Right fork of philosopher p is fork p
LeftFork(p) == (p - 1 + N) % N
RightFork(p) == p

\* The two philosophers adjacent to fork f
LeftPhil(f) == f
RightPhil(f) == (f + 1) % N

\* Neighbor relationship
Neighbors(p, q) == (p = (q + 1) % N) \/ (q = (p + 1) % N)

VARIABLES
    state,          \* state[p] \in {"thinking", "hungry", "eating"}
    forkOwner,      \* forkOwner[f] \in Philosophers (owner of fork f)
    forkClean,      \* forkClean[f] \in BOOLEAN (TRUE if clean, FALSE if dirty)
    forkRequested   \* forkRequested[f] \in BOOLEAN (TRUE if the non-owner has requested it)

vars == <<state, forkOwner, forkClean, forkRequested>>

\* Initially, each fork is held dirty by the lower-numbered of its two adjacent philosophers
\* Fork f is between philosopher f (left) and (f+1) % N (right)
\* Lower numbered is MIN(f, (f+1) % N)
InitialOwner(f) == IF f < (f + 1) % N THEN f ELSE (f + 1) % N

Init ==
    /\ state = [p \in Philosophers |-> "thinking"]
    /\ forkOwner = [f \in Forks |-> InitialOwner(f)]
    /\ forkClean = [f \in Forks |-> FALSE]  \* All forks start dirty
    /\ forkRequested = [f \in Forks |-> FALSE]

\* Type invariant
TypeOK ==
    /\ state \in [Philosophers -> {"thinking", "hungry", "eating"}]
    /\ forkOwner \in [Forks -> Philosophers]
    /\ forkClean \in [Forks -> BOOLEAN]
    /\ forkRequested \in [Forks -> BOOLEAN]

\* Check if philosopher p owns fork f
OwnsFork(p, f) == forkOwner[f] = p

\* Check if philosopher p owns both adjacent forks
OwnsBothForks(p) == OwnsFork(p, LeftFork(p)) /\ OwnsFork(p, RightFork(p))

\* Check if both forks are clean (required to eat)
BothForksClean(p) == forkClean[LeftFork(p)] /\ forkClean[RightFork(p)]

\* The other philosopher sharing fork f with p
OtherPhil(p, f) == IF LeftPhil(f) = p THEN RightPhil(f) ELSE LeftPhil(f)

\* Philosopher p becomes hungry
BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    \* Request forks we don't own
    /\ forkRequested' = [f \in Forks |->
        IF (f = LeftFork(p) \/ f = RightFork(p)) /\ forkOwner[f] # p
        THEN TRUE
        ELSE forkRequested[f]]
    /\ UNCHANGED <<forkOwner, forkClean>>

\* Philosopher p passes a dirty fork f to the requesting neighbor
\* A fork is passed only if: owner has it, it's dirty, it's been requested, and owner is not eating
PassFork(p, f) ==
    /\ forkOwner[f] = p
    /\ forkClean[f] = FALSE  \* Fork must be dirty to be passed
    /\ forkRequested[f] = TRUE
    /\ state[p] # "eating"
    /\ forkOwner' = [forkOwner EXCEPT ![f] = OtherPhil(p, f)]
    /\ forkClean' = [forkClean EXCEPT ![f] = TRUE]  \* Clean before passing
    /\ forkRequested' = [forkRequested EXCEPT ![f] = FALSE]
    /\ UNCHANGED state

\* Philosopher p starts eating (must own both forks and they must be clean)
StartEating(p) ==
    /\ state[p] = "hungry"
    /\ OwnsBothForks(p)
    /\ BothForksClean(p)
    /\ state' = [state EXCEPT ![p] = "eating"]
    /\ UNCHANGED <<forkOwner, forkClean, forkRequested>>

\* Philosopher p finishes eating and starts thinking
\* Both forks become dirty after eating
FinishEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ forkClean' = [f \in Forks |->
        IF f = LeftFork(p) \/ f = RightFork(p)
        THEN FALSE  \* Forks become dirty after eating
        ELSE forkClean[f]]
    /\ UNCHANGED <<forkOwner, forkRequested>>

\* Actions for a specific philosopher
PhilosopherAction(p) ==
    \/ BecomeHungry(p)
    \/ \E f \in {LeftFork(p), RightFork(p)} : PassFork(p, f)
    \/ StartEating(p)
    \/ FinishEating(p)

Next == \E p \in Philosophers : PhilosopherAction(p)

\* Fairness: each philosopher must be fair (weak fairness on their actions)
Fairness == \A p \in Philosophers : WF_vars(PhilosopherAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual exclusion - no two neighbors can eat simultaneously
MutualExclusion ==
    \A p, q \in Philosophers :
        (Neighbors(p, q) /\ state[p] = "eating") => state[q] # "eating"

\* Liveness: No philosopher starves - every hungry philosopher eventually eats
\* Expressed as: it's always the case that if a philosopher is hungry, they eventually eat
NoStarvation == \A p \in Philosophers : [](state[p] = "hungry" => <>(state[p] = "eating"))

\* Alternative formulation: every philosopher eats infinitely often
EatsInfinitelyOften == \A p \in Philosophers : []<>(state[p] = "eating")

=============================================================================