---------------------------- MODULE InstanceInLet ----------------------------
(***************************************************************************)
(* Minimal module used to test an INSTANCE inside a LET context.           *)
(* The modeled state consists of a single variable x, and the only         *)
(* substantive operator, xplus1, computes x + 1 from the current state.    *)
(* No actions, fault model, safety properties or liveness properties are   *)
(* described. Init, Next and Spec are trivial placeholders so that the     *)
(* module is complete.                                                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS InitValue

VARIABLES x

vars == << x >>

xplus1 == x + 1

Init == x = InitValue

(* No actions are described, so the next-state relation only stutters. *)
Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

=============================================================================