------------------------------ MODULE MCTCommit ------------------------------
(***************************************************************************)
(* Model-checking companion module for the transaction commit             *)
(* specification TCommit. It adds two state predicates over rmState:      *)
(* a type-correctness condition and a consistency condition.              *)
(* It adds no actions of its own. Init, Next and Spec are aliases for the *)
(* definitions already in TCommit.                                         *)
(***************************************************************************)
EXTENDS TCommit

(***************************************************************************)
(* Aliases for the behavior defined in TCommit.                           *)
(***************************************************************************)
Init == TCInit

Next == TCNext

Spec == TCSpec

(***************************************************************************)
(* Type correctness: every resource manager is in one of the four named   *)
(* status strings.                                                         *)
(***************************************************************************)
MCTypeOK ==
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

(***************************************************************************)
(* Consistency: no resource manager can be aborted while another one is   *)
(* committed.                                                              *)
(***************************************************************************)
MCConsistent ==
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"

=============================================================================