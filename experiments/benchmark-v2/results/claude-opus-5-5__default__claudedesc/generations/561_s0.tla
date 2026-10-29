---------------------------- MODULE MCTCommit ----------------------------
(***************************************************************************)
(* Model-checking configuration for the transaction commit protocol       *)
(* (TCommit). A set RM of resource managers must either all commit or    *)
(* all abort. The definitions of the base TCommit module are included     *)
(* here so that this module is self-contained.                            *)
(*                                                                         *)
(* Model: RM <- {r1, r2, r3} (model values)                                *)
(* INVARIANTS TCTypeOK TCConsistent                                        *)
(* SPECIFICATION TCSpec                                                    *)
(* CHECK_DEADLOCK FALSE                                                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS r1, r2, r3     \* model values for the three resource managers

CONSTANT RM              \* the set of participating resource managers

\* Model instantiation of RM: the three participants r1, r2, r3
const_RM == {r1, r2, r3}

ASSUME RM # {}

VARIABLE rmState         \* rmState[r] is the state of resource manager r

vars == << rmState >>

-----------------------------------------------------------------------------
(* Base TCommit definitions *)

TCTypeOK ==
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

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

TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

TCSpec == TCInit /\ [][TCNext]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

TCConsistent ==
  \A r1x, r2x \in RM : ~ /\ rmState[r1x] = "aborted"
                         /\ rmState[r2x] = "committed"

-----------------------------------------------------------------------------
(* Model-checking aliases / theorems *)

Init == TCInit
Next == TCNext
Spec == TCSpec

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=============================================================================