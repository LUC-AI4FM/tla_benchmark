---------------------------- MODULE MCTCommit ----------------------------
(***************************************************************************)
(* Model-checking companion module for the transaction commit             *)
(* specification TCommit.  The constant RM, the variable rmState, and the *)
(* definitions Init, Next and Spec are all inherited from TCommit; this   *)
(* module adds only two state predicates over rmState.                    *)
(***************************************************************************)
EXTENDS TCommit

(***************************************************************************)
(* Type correctness: every resource manager is in one of the four named   *)
(* statuses.                                                              *)
(***************************************************************************)
MCTypeOK ==
    rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

(***************************************************************************)
(* Consistency: no resource manager can be aborted while another one is   *)
(* committed.                                                             *)
(***************************************************************************)
MCConsistent ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                         /\ rmState[r2] = "committed"

=============================================================================