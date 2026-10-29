------------------------------ MODULE TCommit ------------------------------
(***************************************************************************)
(* A simplified, single-node view of the Two-Phase Commit protocol.        *)
(* Each resource manager (RM) can be "working", "prepared", "committed",   *)
(* or "aborted".                                                           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT RM       \* The set of participating resource managers

VARIABLE rmState  \* rmState[r] is the state of resource manager r

vars == << rmState >>

TCTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant.                                       *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit ==
  (*************************************************************************)
  (* Initially every RM is working.                                        *)
  (*************************************************************************)
  rmState = [r \in RM |-> "working"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}
  \* True iff all RMs are prepared or committed.

notCommitted == \A r \in RM : rmState[r] # "committed"
  \* True iff no RM has committed.

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

TCSpec == TCInit /\ [][TCNext]_rmState

TCConsistent ==
  (*************************************************************************)
  (* No RM is aborted while another is committed.                          *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)

(***************************************************************************)
(* Model-checking configuration (TCommit.cfg):                             *)
(*   CONSTANT RM = {r1, r2, r3}                                            *)
(*   SPECIFICATION TCSpec                                                  *)
(*   INVARIANT TCTypeOK TCConsistent                                       *)
(*   CHECK_DEADLOCK FALSE                                                  *)
(***************************************************************************)
=============================================================================