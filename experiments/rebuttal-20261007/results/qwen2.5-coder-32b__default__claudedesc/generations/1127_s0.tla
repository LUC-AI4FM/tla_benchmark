------------------------------- MODULE TwoPhaseCommit -------------------------------
EXTENDS TLC, FiniteSets

CONSTANTS RM

VARIABLES rmState

Init == /\ rmState \in [RM -> {"working"}]

Prepare(r) == 
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

DecideCommit(r) ==
    /\ rmState[r] = "prepared"
    /\ (\A r' \in RM: rmState[r'] \in {"prepared", "committed"})
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ (\A r' \in RM: rmState[r'] \notin {"committed"})
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == 
    \/ (\E r \in RM: Prepare(r))
    \/ (\E r \in RM: DecideCommit(r))
    \/ (\E r \in RM: DecideAbort(r))

Spec == Init /\ [][TCNext]_<<rmState>>

TCTypeOK ==
    rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCConsistent ==
    ~(\E r1, r2 \in RM: rmState[r1] = "aborted" /\ rmState[r2] = "committed")

=============================================================================