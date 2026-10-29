---------------------------- MODULE MCTCommit ----------------------------
(***************************************************************************)
(* Model-checking companion module for the transaction commit             *)
(* specification TCommit.  It adds two state predicates over rmState:     *)
(*   - TypeOK:     each resource manager is in one of four named states.   *)
(*   - Consistent: no resource manager has aborted while another one has   *)
(*                 committed.                                              *)
(* The constant RM and the variable rmState come from TCommit, along with  *)
(* TCInit, TCNext and TCSpec.  Init, Next and Spec are aliases for those   *)
(* operators, so this module adds no actions of its own.                   *)
(***************************************************************************)
EXTENDS TCommit

TypeOK ==
  (*************************************************************************)
  (* Type-correctness: every resource manager is in one of the four        *)
  (* status strings.                                                       *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

Consistent ==
  (*************************************************************************)
  (* Consistency: no resource manager is "aborted" while another one is    *)
  (* "committed".                                                          *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"

(***************************************************************************)
(* Aliases for the behavior defined in TCommit, for use in a model.        *)
(***************************************************************************)
Init == TCInit

Next == TCNext

Spec == TCSpec

=============================================================================