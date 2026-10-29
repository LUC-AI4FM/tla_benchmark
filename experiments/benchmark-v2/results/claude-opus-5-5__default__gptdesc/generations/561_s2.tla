------------------------------ MODULE MCTCommit ------------------------------
(***************************************************************************)
(* Model-checking companion module for the transaction commit              *)
(* specification TCommit.  TCommit declares the constant RM (the set of    *)
(* resource managers) and the variable rmState.  This module only adds two *)
(* state predicates over rmState.  It defines no new actions, temporal     *)
(* behavior, fairness conditions or proofs.  Init, Next and Spec simply    *)
(* rename the corresponding definitions of TCommit for use by TLC.         *)
(***************************************************************************)
EXTENDS TCommit

(***************************************************************************)
(* Type correctness: each resource manager is in one of the four named     *)
(* status strings.                                                         *)
(***************************************************************************)
TypeOK ==
    rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

(***************************************************************************)
(* Consistency: no two resource managers can be such that one has aborted *)
(* while the other has committed.                                          *)
(***************************************************************************)
Consistent ==
    \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                          /\ rmState[rm2] = "committed"

(***************************************************************************)
(* Aliases for the behavior defined in TCommit.  No new behavior is added. *)
(***************************************************************************)
Init == TCInit

Next == TCNext

Spec == TCSpec

=============================================================================