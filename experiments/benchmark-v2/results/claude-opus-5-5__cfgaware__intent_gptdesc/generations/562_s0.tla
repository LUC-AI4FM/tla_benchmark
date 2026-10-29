------------------------------- MODULE TCommit -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT RM

ASSUME RM # {}

VARIABLE rmState

vars == << rmState >>

States == {"working", "prepared", "committed", "aborted"}

TCTypeOK == rmState \in [RM -> States]

TCInit == rmState = [r \in RM |-> "working"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] # "committed"

Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r) ==
    \/ /\ rmState[r] = "prepared"
       /\ canCommit
       /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    \/ /\ rmState[r] \in {"working", "prepared"}
       /\ notCommitted
       /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Commit(r) ==
    /\ rmState[r] = "prepared"
    /\ canCommit
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

Abort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ notCommitted
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : Prepare(r) \/ Commit(r) \/ Abort(r)

TCFairness ==
    \A r \in RM : /\ WF_vars(Commit(r))
                  /\ WF_vars(Abort(r))

TCSpec == TCInit /\ [][TCNext]_vars /\ TCFairness

-----------------------------------------------------------------------------
(* Safety *)

TCConsistent ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                         /\ rmState[r2] = "committed"

CommittedStable ==
    [][\A r \in RM : rmState[r] = "committed" => rmState'[r] = "committed"]_vars

NoAbortAfterCommit ==
    [][(\E r \in RM : rmState[r] = "committed")
          => (\A r \in RM : rmState'[r] # "aborted")]_vars

(* Liveness *)

AllPreparedLeadsToDecision ==
    (\A r \in RM : rmState[r] = "prepared")
        ~> (\A r \in RM : rmState[r] \in {"committed", "aborted"})

CommitPropagates ==
    (\E r \in RM : rmState[r] = "committed")
        ~> (\A r \in RM : rmState[r] = "committed")

AbortPropagates ==
    (\E r \in RM : rmState[r] = "aborted")
        ~> (\A r \in RM : rmState[r] = "aborted")

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=============================================================================