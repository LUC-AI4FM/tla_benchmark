---------------------------- MODULE MCTCommit ----------------------------
(***************************************************************************)
(* Transaction commit specification with model-checking configuration.    *)
(* Self-contained version of the TCommit spec: a set of resource managers *)
(* RM must either all commit or all abort.                                 *)
(***************************************************************************)

CONSTANT RM       \* The set of participating resource managers

VARIABLE rmState  \* rmState[r] is the state of resource manager r.

-----------------------------------------------------------------------------

TCTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant.                                       *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit ==
  (*************************************************************************)
  (* Initially, every resource manager is working.                         *)
  (*************************************************************************)
  rmState = [r \in RM |-> "working"]

canCommit ==
  (*************************************************************************)
  (* All RMs are prepared or some RM has already committed.                *)
  (*************************************************************************)
  \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted ==
  (*************************************************************************)
  (* No RM has decided to commit.                                          *)
  (*************************************************************************)
  \A r \in RM : rmState[r] # "committed"

-----------------------------------------------------------------------------

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

TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

-----------------------------------------------------------------------------

TCConsistent ==
  (*************************************************************************)
  (* No two RMs disagree: one committed while another aborted.             *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

TCSpec == TCInit /\ [][TCNext]_rmState

-----------------------------------------------------------------------------

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=============================================================================