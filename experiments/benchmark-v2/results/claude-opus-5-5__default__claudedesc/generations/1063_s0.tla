--------------------------- MODULE EWD840_json ---------------------------
(***************************************************************************)
(* Extends Dijkstra's token-ring termination detection algorithm (EWD 840) *)
(* with JSON trace export for debugging.                                   *)
(*                                                                         *)
(* No constants, variables, Init, Next or Spec are defined here. They are  *)
(* all inherited from the base module EWD840, including the constant N,    *)
(* the variables, Init, Next, Spec and the safety invariant Inv.           *)
(* Redefining any of them would be a multiple-definition error in SANY.    *)
(*                                                                         *)
(* Configuration (EWD840_json.cfg):                                        *)
(*   CONSTANT N = 4                                                        *)
(*   SPECIFICATION Spec                                                    *)
(*   CHECK_DEADLOCK FALSE                                                  *)
(*   INVARIANT JsonInv                                                     *)
(***************************************************************************)
EXTENDS EWD840, TLC, TLCExt, Json

(***************************************************************************)
(* JsonInv wraps the real invariant Inv of EWD840.                         *)
(*                                                                         *)
(* If Inv holds in the current state, the first disjunct is TRUE and TLC   *)
(* never evaluates the second disjunct.                                    *)
(*                                                                         *)
(* If Inv is violated, TLC evaluates the second disjunct. It writes the    *)
(* current execution trace (TLCExt!Trace) to "trace.json" and sets TLC's   *)
(* "exit" register. TLC then terminates cleanly instead of printing the    *)
(* usual text error trace.                                                 *)
(***************************************************************************)
JsonInv ==
    \/ Inv
    \/ /\ JsonSerialize("trace.json", Trace)
       /\ TLCSet("exit", TRUE)

=============================================================================