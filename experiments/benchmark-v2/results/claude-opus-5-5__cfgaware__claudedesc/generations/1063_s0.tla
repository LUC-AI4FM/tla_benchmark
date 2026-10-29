---------------------------- MODULE EWD840_json ----------------------------
(***************************************************************************)
(* Extends Dijkstra's token-ring termination detection algorithm (EWD 840) *)
(* with an invariant that exports the counterexample trace as JSON.        *)
(*                                                                         *)
(* N and Spec are inherited from the EWD840 module.                        *)
(*                                                                         *)
(* If Inv holds, the first disjunct is TRUE and TLC is satisfied. If Inv   *)
(* fails, TLC evaluates the second disjunct. That disjunct writes the      *)
(* current trace to "trace.json". It then tells TLC to exit cleanly        *)
(* without printing the usual text error trace.                            *)
(***************************************************************************)
EXTENDS EWD840, Json, TLC, TLCExt

JsonInv ==
    \/ Inv
    \/ /\ JsonSerialize("trace.json", Trace)
       /\ TLCSet("exit", TRUE)

=============================================================================