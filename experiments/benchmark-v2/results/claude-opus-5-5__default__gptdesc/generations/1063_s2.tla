--------------------------- MODULE EWD840_json ---------------------------
(***************************************************************************)
(* JSON-exporting invariant wrapper around the EWD840 specification.      *)
(* No new algorithm is introduced: Init, Next, Spec, Inv, TypeOK, etc.    *)
(* are all imported from the extended module EWD840.                      *)
(*                                                                         *)
(* Check JsonInv as an invariant (instead of Inv). TLC evaluates the       *)
(* disjuncts of JsonInv from left to right:                                *)
(*   - If the real invariant Inv holds, the first disjunct is TRUE and     *)
(*     the Export branch is never evaluated.                               *)
(*   - If Inv is violated, TLC evaluates the Export branch, which          *)
(*     serializes the current behavior (Trace) to trace.json and sets      *)
(*     TLC's "exit" flag, so model checking stops without the usual        *)
(*     textual error trace (unless that flag is changed).                  *)
(***************************************************************************)
EXTENDS EWD840, TLC, TLCExt, Json

-----------------------------------------------------------------------------
(* Re-exposed definitions from EWD840, for clarity in the model config.    *)

JsonInit == Init

JsonNext == Next

JsonSpec == Spec

-----------------------------------------------------------------------------
(* The JSON-exporting invariant.                                           *)

JsonInv ==
    \/ Inv
    \/ Export:: /\ JsonSerialize("trace.json", Trace)
                /\ TLCSet("exit", TRUE)

=============================================================================