------------------------------ MODULE TCommit ------------------------------
(***************************************************************************)
(* This specification describes the transaction commit protocol for a set  *)
(* of resource managers (RMs).  Each RM may be in the state "working",     *)
(* "prepared", "committed", or "aborted".                                  *)
(***************************************************************************)
CONSTANT RM       \* The set of participating resource managers

VARIABLE rmState  \* rmState[r] is the state of resource manager r.

vars == << rmState >>

-----------------------------------------------------------------------------
TCTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant.                                       *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit ==
  (*************************************************************************)
  (* The initial predicate: every RM starts in the "working" state.        *)
  (*************************************************************************)
  rmState = [r \in RM |-> "working"]

canCommit ==
  (*************************************************************************)
  (* True iff all RMs are in the "prepared" or "committed" state.          *)
  (*************************************************************************)
  \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted ==
  (*************************************************************************)
  (* True iff no RM is in the "committed" state.                           *)
  (*************************************************************************)
  \A r \in RM : rmState[r] # "committed"

-----------------------------------------------------------------------------
(***************************************************************************)
(* The actions that may be performed by resource manager r.                *)
(***************************************************************************)
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

TCNext ==
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
  \E r \in RM : Prepare(r) \/ Decide(r)

-----------------------------------------------------------------------------
TCConsistent ==
  (*************************************************************************)
  (* The safety invariant: no two RMs disagree, i.e., it is never the case *)
  (* that one RM has aborted while another has committed.                  *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

-----------------------------------------------------------------------------
TCSpec == TCInit /\ [][TCNext]_rmState
  (*************************************************************************)
  (* The complete specification: start in TCInit and take only TCNext     *)
  (* steps or stuttering steps.  No fairness is assumed.                   *)
  (*************************************************************************)

Spec == TCSpec

-----------------------------------------------------------------------------
THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=============================================================================