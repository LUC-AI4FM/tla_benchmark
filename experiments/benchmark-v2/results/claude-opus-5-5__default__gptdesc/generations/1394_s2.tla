---------------------------- MODULE Github702 ----------------------------
(***************************************************************************)
(* Models a TLC issue (GitHub #702). During next-state computation, an     *)
(* identifier substituted for an instantiated variable used to become      *)
(* undefined when it appeared inside an UNCHANGED expression.              *)
(*                                                                         *)
(* The module x_unchanged is defined as an inner module before any outer   *)
(* declarations, so that it does not inherit y and z from this module. It  *)
(* is then instantiated with the substitution x <- fizzbuzz, where         *)
(* fizzbuzz is a constant-valued operator. The variables y and z are       *)
(* substituted implicitly by the same-named variables of this module.      *)
(***************************************************************************)

---------------------------- MODULE x_unchanged ----------------------------
EXTENDS Naturals

VARIABLES x, y, z

Init ==
    /\ x \in {1, 2, 3}
    /\ y \in {1, 2, 3}
    /\ z \in {1, 2, 3}

Next ==
    /\ y' = y + 1
    /\ UNCHANGED <<x, z>>

Spec == Init /\ [][Next]_<<x, y, z>>
=============================================================================