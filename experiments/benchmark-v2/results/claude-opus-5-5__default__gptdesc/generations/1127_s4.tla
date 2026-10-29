------------------------------ MODULE TCommit ------------------------------
(***************************************************************************)
(* Specification of the Transaction Commit problem underlying Two-Phase    *)
(* Commit. Each resource manager (RM) is in one of the states "working",   *)
(* "prepared", "committed", or "aborted". The RMs either all commit or all *)
(* abort. No coordinator or message passing is modeled.                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT RM          \* The set of participating resource managers

VARIABLE rmState     \* rmState[r] is the state of resource manager r

vars == << rmState >>

-----------------------------------------------------------------------------
TCTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant.                                       *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit ==
  (*************************************************************************)
  (* Initially every RM is in the "working" state.                         *)
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
  (* The next-state relation: some RM performs Prepare or Decide.          *)
  (*************************************************************************)
  \E r \in RM : Prepare(r) \/ Decide(r)

-----------------------------------------------------------------------------
TCSpec == TCInit /\ [][TCNext]_vars

-----------------------------------------------------------------------------
TCConsistent ==
  (*************************************************************************)
  (* No two RMs reach conflicting decisions: it is never the case that one *)
  (* RM has aborted while another has committed.                           *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

-----------------------------------------------------------------------------
THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=============================================================================