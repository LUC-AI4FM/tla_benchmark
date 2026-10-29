---------------------------- MODULE TestInstanceInLet ----------------------------
(***************************************************************************)
(* Minimal module used to test an INSTANCE inside a LET context.           *)
(* The state consists of a single variable x, and the only substantive     *)
(* operator xplus1 computes x + 1 from the current state.                  *)
(*                                                                         *)
(* The original description has no actions, no temporal specification,    *)
(* and no verified properties. The Init, Next and Spec below are trivial   *)
(* additions to give a complete module skeleton. Next only stutters, so    *)
(* the behaviour is unchanged.                                             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS InitVal

VARIABLES x

vars == <<x>>

xplus1 == x + 1

Init == x = InitVal

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

=============================================================================