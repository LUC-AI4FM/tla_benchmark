------------------------------- MODULE TwoPhaseCommitTC -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT RM

VARIABLE rmState

vars == << rmState >>

States == {"working", "prepared", "committed", "aborted"}

TypeOK == rmState \in [RM -> States]

Init == rmState = [r \in RM |-> "working"]

(* Commit is allowed only when every participant is prepared or has committed. *)
CanCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

(* Abort is allowed only while no participant has committed. *)
NotCommitted == \A r \in RM : rmState[r] # "committed"

Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

DecideCommit(r) ==
    /\ rmState[r] = "prepared"
    /\ CanCommit
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ NotCommitted
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Decide(r) == DecideCommit(r) \/ DecideAbort(r)

Next == \E r \in RM : Prepare(r) \/ Decide(r)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

Consistent ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                         /\ rmState[r2] = "committed"

AllPrepared == \A r \in RM : rmState[r] = "prepared"

(* Once all participants are prepared, a commit decision is enabled. *)
CommitPossible ==
    AllPrepared => \A r \in RM : ENABLED DecideCommit(r)

Inv == TypeOK /\ Consistent /\ CommitPossible

THEOREM Spec => [](TypeOK /\ Consistent /\ CommitPossible)
=============================================================================