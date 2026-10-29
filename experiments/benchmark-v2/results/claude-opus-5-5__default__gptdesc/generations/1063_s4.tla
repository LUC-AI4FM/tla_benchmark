---------------------------- MODULE EWD840_json ----------------------------
(***************************************************************************)
(* JSON-exporting invariant wrapper around the EWD840 specification.      *)
(*                                                                         *)
(* No new algorithm is introduced: the constants, variables, Init, Next,  *)
(* Spec, the invariant Inv, and the fairness and liveness properties all  *)
(* come from the extended module EWD840.                                   *)
(*                                                                         *)
(* Check the model with JsonInv as the invariant, in place of Inv.         *)
(*                                                                         *)
(* TLC evaluates the disjuncts of JsonInv from left to right:              *)
(*   - If Inv holds, the first disjunct is TRUE. TLC never evaluates the   *)
(*     Export branch, so nothing is written.                               *)
(*   - If Inv is violated, TLC evaluates Export. Export does two things:   *)
(*       1. It serializes the current execution trace (TLCExt!Trace) to    *)
(*          the file trace.json.                                           *)
(*       2. It sets TLC's "exit" register, so model checking stops.        *)
(*                                                                         *)
(* Export evaluates to TRUE, so TLC does not report an invariant           *)
(* violation. As a result, it does not print the usual textual error       *)
(* trace. If you change the exit flag in Export, TLC behaves differently.  *)
(***************************************************************************)
EXTENDS EWD840, Json, TLC, TLCExt

Export ==
    /\ JsonSerialize("trace.json", Trace)
    /\ TLCSet("exit", TRUE)

JsonInv ==
    \/ Inv
    \/ Export

=============================================================================