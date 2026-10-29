------------------------------ MODULE MCMultiNodeReads ------------------------------
(***************************************************************************)
(* Bounded model-checking wrapper for the multi-node reads specification. *)
(* The state variables, constants, Init, the underlying multi-node        *)
(* transition (MultiNodeNext), and the read-only transaction actions      *)
(* (ReadOnlyTxnRequest, ReadOnlyTxnResponse) are all defined in the       *)
(* extended modules. This module only composes them into a combined       *)
(* next-state relation and a safety-style temporal specification.         *)
(***************************************************************************)

EXTENDS MultiNodeReads, ReadOnlyTransactions

(***************************************************************************)
(* Combined next-state action: either a step of the underlying multi-node *)
(* system, or a read-only transaction request or response.               *)
(***************************************************************************)
MCNext ==
    \/ MultiNodeNext
    \/ ReadOnlyTxnRequest
    \/ ReadOnlyTxnResponse

(***************************************************************************)
(* Safety-style specification: no fairness conditions.                    *)
(***************************************************************************)
MCSpec == Init /\ [][MCNext]_vars

=====================================================================================