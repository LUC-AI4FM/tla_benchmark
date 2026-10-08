---------------------------- MODULE BarrierSync ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

VARIABLES
    state,      \* state[p] \in {"approaching", "arrived"} for each process p
    released    \* flag indicating barrier release has occurred (for action property)

Procs == 1..N

vars == <<state, released>>

TypeOK ==
    /\ state \in [Procs -> {"approaching", "arrived"}]
    /\ released \in BOOLEAN

\* All processes have arrived at the barrier
AllArrived == \A p \in Procs : state[p] = "arrived"

\* At least one process has not yet arrived
SomeNotArrived == \E p \in Procs : state[p] = "approaching"

\* At least one process has arrived
SomeArrived == \E p \in Procs : state[p] = "arrived"

Init ==
    /\ state = [p \in Procs |-> "approaching"]
    /\ released = FALSE

\* A process arrives at the barrier
Arrive(p) ==
    /\ state[p] = "approaching"
    /\ state' = [state EXCEPT ![p] = "arrived"]
    /\ released' = FALSE

\* All processes are released together when all have arrived
\* This is atomic - all processes return to approaching state together
Release ==
    /\ AllArrived
    /\ state' = [p \in Procs |-> "approaching"]
    /\ released' = TRUE

Next ==
    \/ \E p \in Procs : Arrive(p)
    \/ Release

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: No process can leave (be released) while any other process has not arrived
\* This is expressed as: if a release happens, all processes must have been arrived
\* We check this as an action property: whenever state changes from arrived to approaching,
\* all processes must have been in arrived state

\* A process p is being released (transitioning from arrived to approaching)
BeingReleased(p) == state[p] = "arrived" /\ state'[p] = "approaching"

\* The barrier property: if any process is being released, all must have been arrived
\* This ensures no premature release - a process cannot leave while others haven't arrived
BarrierProperty ==
    (\E p \in Procs : BeingReleased(p)) => AllArrived

\* Stuttering-tolerant version: either vars don't change, or barrier property holds
BarrierSafety == [][BarrierProperty]_vars

\* Alternative safety invariant: it's never the case that some process is approaching
\* while we're in a state where release just happened (captured by released flag)
\* But the action property above is more precise

\* Liveness: Eventually all processes will be released (barrier will complete)
Liveness == []<>(AllArrived)

\* Liveness: The barrier will eventually release and processes return to approaching
EventualRelease == []<>(\A p \in Procs : state[p] = "approaching")

=============================================================================