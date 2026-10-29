------------------------------ MODULE Github702 ------------------------------
(***************************************************************************)
(* Models a TLC issue (GitHub #702) where an identifier becomes undefined  *)
(* inside an UNCHANGED expression during next-state computation.  The      *)
(* module x_unchanged declares a variable x.  It is instantiated here with *)
(* the substitution x <- fizzbuzz, where fizzbuzz is a constant-valued     *)
(* operator.  Because of that, UNCHANGED <<x, z>> in x_unchanged becomes   *)
(* UNCHANGED <<fizzbuzz, z>> in this module.                               *)
(***************************************************************************)

---------------------------- MODULE x_unchanged ----------------------------
EXTENDS Naturals

VARIABLES x, y, z

Init == /\ x \in {1, 2, 3}
        /\ y \in {1, 2, 3}
        /\ z \in {1, 2, 3}

Next == /\ y' = y + 1
        /\ UNCHANGED <<x, z>>

Spec == Init /\ [][Next]_<<x, y, z>>
=============================================================================