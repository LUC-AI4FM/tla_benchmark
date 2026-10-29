------------------------------- MODULE EWD840_json -------------------------------
(***************************************************************************)
(* JSON-exporting invariant wrapper around the EWD840 specification.      *)
(* No new algorithm is introduced. All constants (N), variables (active,   *)
(* color, tpos, tcolor), Init, Next, Spec and the invariant Inv are         *)
(* imported from the extended module EWD840.                               *)
(*                                                                         *)
(* The wrapper relies on how TLC evaluates the disjuncts of JsonInv:       *)
(*  - If Inv holds, the first disjunct is TRUE and Export is never         *)
(*    evaluated.                                                           *)
(*  - If Inv is violated, TLC evaluates the Export disjunct. That disjunct *)
(*    serializes the current execution trace (Trace) to trace.json and     *)
(*    sets TLC's "exit" flag.                                              *)
(*                                                                         *)
(* With the flag set, model checking stops without printing the usual     *)
(* textual error trace. To get TLC's regular error report as well, change  *)
(* the flag or the conjunct value.                                         *)
(***************************************************************************)
EXTENDS EWD840, TLC, TLCExt, Json

\* Aliases that re-expose the imported definitions under the wrapper's names.
JsonInit == Init
JsonNext == Next
JsonSpec == Spec

JsonInv ==
    \/ Inv:: Inv
    \/ Export:: /\ JsonSerialize("trace.json", Trace)
                /\ TLCSet("exit", TRUE)

=============================================================================