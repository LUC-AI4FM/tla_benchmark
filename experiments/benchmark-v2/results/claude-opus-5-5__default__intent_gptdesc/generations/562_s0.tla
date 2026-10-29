------------------------------ MODULE TwoPhaseCommitRM ------------------------------
EXTENDS FiniteSets

CONSTANT RM

ASSUME RMAssumption == RM # {} /\ IsFiniteSet(RM)

VARIABLE rmState

vars == << rmState >>

States == {"working", "prepared", "committed", "aborted"}

TypeOK == rmState \in [RM -> States]

Init == rmState = [r \in RM |-> "working"]

-----------------------------------------------------------------------------
(* Predicates on the global state                                          *)
-----------------------------------------------------------------------------

CanCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

NotCommitted == \A r \in RM : rmState[r] # "committed"

AllPrepared == \A r \in RM : rmState[r] = "prepared"

AllCommitted == \A r \in RM : rmState[r] = "committed"

SomeCommitted == \E r \in RM : rmState[r] = "committed"

SomeAborted == \E r \in RM : rmState[r] = "aborted"

-----------------------------------------------------------------------------
(* Actions                                                                 *)
-----------------------------------------------------------------------------

Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r) ==
    \/ /\ rmState[r] = "prepared"
       /\ CanCommit
       /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    \/ /\ rmState[r] \in {"working", "prepared"}
       /\ NotCommitted
       /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Commit(r) ==
    /\ rmState[r] = "prepared"
    /\ CanCommit
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

Abort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ NotCommitted
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Next == \E r \in RM : Prepare(r) \/ Commit(r) \/ Abort(r)

(* Fairness: every resource manager that can prepare eventually does so,  *)
(* and every resource manager that can commit eventually does so.          *)
(* Aborts are allowed but not forced (no fairness on Abort).               *)
Fairness ==
    /\ \A r \in RM : WF_vars(Prepare(r))
    /\ \A r \in RM : WF_vars(Commit(r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties                                                       *)
-----------------------------------------------------------------------------

(* (1) A committed resource manager never leaves the committed state. *)
CommittedStable ==
    [][\A r \in RM : rmState[r] = "committed" => rmState'[r] = "committed"]_vars

(* (2) No conflicting global outcomes: committed and aborted never coexist. *)
Consistent ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "committed"
                         /\ rmState[r2] = "aborted"

(* (2') Once any resource manager commits, no resource manager later aborts. *)
NoAbortAfterCommit ==
    [][SomeCommitted => \A r \in RM : rmState'[r] # "aborted"]_vars

(* Aborted is also a final state. *)
AbortedStable ==
    [][\A r \in RM : rmState[r] = "aborted" => rmState'[r] = "aborted"]_vars

-----------------------------------------------------------------------------
(* Liveness properties                                                     *)
-----------------------------------------------------------------------------

(* If all resource managers become prepared, a commit decision is then     *)
(* possible, and a decision is eventually taken: commit, unless an abort   *)
(* intervened before any commit.                                           *)
CommitPossibleWhenPrepared == AllPrepared => CanCommit

PreparedLeadsToDecision ==
    AllPrepared ~> (SomeCommitted \/ SomeAborted)

(* Once a commit decision is taken, all resource managers commit. *)
CommitLeadsToAllCommitted ==
    SomeCommitted ~> AllCommitted

(* If some resource manager aborts while none have committed, the system  *)
(* settles on abort: no resource manager ever commits afterwards.          *)
AbortIsFinal ==
    (SomeAborted /\ NotCommitted) ~> [](NotCommitted)

(* Every execution eventually reaches a global decision. *)
EventuallyDecided ==
    <>(AllCommitted \/ SomeAborted)

=============================================================================