---------------------------- MODULE InstanceInLet ----------------------------
(***************************************************************************)
(* Minimal module used to test an INSTANCE inside a LET context.          *)
(* The state consists of a single variable x, and the only operator of    *)
(* interest, xplus1, computes x + 1 from the current state.               *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES x

vars == <<x>>

xplus1 == x + 1

(***************************************************************************)
(* The described module has no actions. The required Init/Next/Spec are   *)
(* given trivially: x starts at 0 and never changes (Next only stutters). *)
(***************************************************************************)
Init == x = 0

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

(* No safety or liveness properties are verified by this module. *)
TypeOK == x \in Nat

=============================================================================