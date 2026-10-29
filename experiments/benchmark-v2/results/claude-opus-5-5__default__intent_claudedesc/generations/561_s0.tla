------------------------------ MODULE TCommit ------------------------------
(***************************************************************************)
(* Specification of the transaction commit problem.  A set RM of resource  *)
(* managers must reach agreement on whether to commit or abort a           *)
(* transaction.  No RM may commit while another aborts.                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT RM          \* The set of participating resource managers

VARIABLE rmState     \* rmState[r] is the state of resource manager r

vars == << rmState >>

-----------------------------------------------------------------------------
TCTypeOK ==
  (*************************************************************************)
  (* Type-correctness invariant.                                           *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit ==
  (*************************************************************************)
  (* Every RM starts in the "working" state.                               *)
  (*************************************************************************)
  rmState = [r \in RM |-> "working"]

canCommit ==
  (*************************************************************************)
  (* An RM may commit only if all RMs are prepared or some RM has          *)
  (* already committed.                                                    *)
  (*************************************************************************)
  \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted ==
  (*************************************************************************)
  (* An RM may abort only if no RM has committed.                          *)
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
TCSpec == TCInit /\ [][TCNext]_vars

Spec == TCSpec

-----------------------------------------------------------------------------
TCConsistent ==
  (*************************************************************************)
  (* Critical safety property: no two RMs reach conflicting decisions.     *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

-----------------------------------------------------------------------------
THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=============================================================================