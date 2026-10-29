---------------------------- MODULE EWD840_json ----------------------------
(***************************************************************************)
(* JSON-exporting invariant wrapper around the EWD840 specification.       *)
(* The constant N, the behavior Spec, and the invariant Inv are all        *)
(* imported from the extended module EWD840.                               *)
(*                                                                         *)
(* TLC evaluates the disjuncts of JsonInv from left to right. If Inv is    *)
(* TRUE, the second disjunct is never evaluated. If Inv is FALSE, TLC      *)
(* evaluates Export. Export serializes the current trace to trace.json and *)
(* sets the TLC "exit" flag, so model checking stops without printing the  *)
(* usual textual error trace. To get the textual error trace as well,      *)
(* change TLCSet("exit", TRUE) to TLCSet("exit", FALSE) and change the     *)
(* final conjunct of Export to FALSE.                                      *)
(***************************************************************************)
EXTENDS EWD840, TLC, TLCExt, Json

\* Trace exporter: writes the behavior that leads to the violation.
Export ==
    /\ JsonSerialize("trace.json", Trace)
    /\ TLCSet("exit", TRUE)

JsonInv ==
    \/ Inv
    \/ Export

=============================================================================