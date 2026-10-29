------------------------------- MODULE EWD840_json -------------------------------
(***************************************************************************)
(* JSON-exporting invariant wrapper around the EWD840 specification.       *)
(*                                                                         *)
(* This module adds no new algorithm. The constants (N), the variables     *)
(* (active, color, tpos, tcolor), Init, Next, Spec, fairness conditions,   *)
(* and the invariant Inv all come from the extended module EWD840.         *)
(* Re-declaring them here would cause name clashes, so this module only    *)
(* refers to them.                                                         *)
(*                                                                         *)
(* How it works:                                                           *)
(*   TLC evaluates the disjuncts of JsonInv from left to right.            *)
(*   - If Inv holds, JsonInv is TRUE and Export is never evaluated.        *)
(*   - If Inv is violated, TLC evaluates Export. Export serializes the     *)
(*     current execution trace (TLCExt!Trace) to trace.json and sets the   *)
(*     TLC "exit" flag. Model checking then stops without reporting an     *)
(*     invariant violation or printing the usual textual error trace.      *)
(*   To also get the textual error trace, change TLCSet("exit", TRUE)      *)
(*   to a conjunct that evaluates to FALSE, for example by adding          *)
(*   /\ FALSE at the end of Export.                                        *)
(*                                                                         *)
(* Example TLC config:                                                     *)
(*   CONSTANT N = 3                                                        *)
(*   SPECIFICATION JsonSpec                                                *)
(*   INVARIANT JsonInv                                                     *)
(***************************************************************************)
EXTENDS EWD840, Json, TLC, TLCExt

-----------------------------------------------------------------------------
(* Names for the inherited Init, Next and Spec, so this wrapper module     *)
(* can be used as the root module of a TLC model.                          *)

JsonInit == Init

JsonNext == Next

JsonSpec == Spec

-----------------------------------------------------------------------------
(* Writes the current behavior to trace.json and asks TLC to exit.         *)

Export ==
    /\ JsonSerialize("trace.json", Trace)
    /\ TLCSet("exit", TRUE)

(* The wrapper invariant. Export is evaluated only when Inv is FALSE.      *)

JsonInv ==
    \/ Inv
    \/ Export

-----------------------------------------------------------------------------
(* The safety property inherited from EWD840, restated as a theorem about  *)
(* the wrapped specification.                                              *)

THEOREM JsonSpec => []Inv

=============================================================================