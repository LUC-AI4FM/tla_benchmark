------------------------------ MODULE Github702 ------------------------------
EXTENDS Naturals

(***************************************************************************)
(* Regression test for a TLC bug fix (GitHub issue #702).                  *)
(* In this module, the variable x of the instantiated module x_unchanged   *)
(* is bound to the constant-valued operator fizzbuzz, not to a variable.   *)
(* TLC must resolve fizzbuzz inside the UNCHANGED <<x, z>> clause of the   *)
(* instantiated Next action. It must not report that the identifier is     *)
(* undefined in an UNCHANGED expression.                                   *)
(*                                                                         *)
(* The model is run with deadlock checking disabled.                       *)
(***************************************************************************)

---------------------------- MODULE x_unchanged -----------------------------
VARIABLES x, y, z

vars == <<x, y, z>>

Init ==
    /\ x \in {1, 2, 3}
    /\ y \in {1, 2, 3}
    /\ z \in {1, 2, 3}

Next ==
    /\ y' = y + 1
    /\ UNCHANGED <<x, z>>

Spec == Init /\ [][Next]_vars
=============================================================================