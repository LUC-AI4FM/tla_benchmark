---------------------------- MODULE EWD840_json ----------------------------
(***************************************************************************)
(* JSON-exporting invariant wrapper around the EWD840 specification.        *)
(*                                                                         *)
(* This module adds no new algorithm. The constant N, the variables        *)
(* active, color, tpos and tcolor, and the definitions Init, Next, Spec    *)
(* and Inv all come from the extended module EWD840.                       *)
(*                                                                         *)
(* To use it, model-check JsonSpec and check the invariant JsonInv instead *)
(* of Inv.                                                                 *)
(*                                                                         *)
(* TLC evaluates the disjuncts of JsonInv from left to right:              *)
(*   - While the real invariant Inv holds, the first disjunct is TRUE and  *)
(*     the Export branch is never evaluated.                               *)
(*   - When Inv is violated, TLC evaluates the Export branch. That branch  *)
(*     serializes the current execution Trace to trace.json and sets the   *)
(*     TLC "exit" flag. Model checking then stops without printing the     *)
(*     usual textual error trace.                                          *)
(*                                                                         *)
(* To get the standard error trace in addition to the JSON file, change    *)
(* TLCSet("exit", TRUE) to TLCSet("exit", FALSE), or remove that conjunct. *)
(***************************************************************************)
EXTENDS EWD840, Json, TLC, TLCExt

(***************************************************************************)
(* The initial predicate, next-state relation and behaviour specification  *)
(* are those of EWD840. They are re-exposed here under distinct names.     *)
(***************************************************************************)
JsonInit == Init
JsonNext == Next
JsonSpec == Spec

(***************************************************************************)
(* The wrapped invariant.                                                  *)
(***************************************************************************)
JsonInv ==
    \/ Inv
    \/ Export:: /\ JsonSerialize("trace.json", Trace)
                /\ TLCSet("exit", TRUE)

=============================================================================