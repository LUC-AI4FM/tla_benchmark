---------------------------- MODULE Github702 ----------------------------
(***************************************************************************)
(* Models a TLC issue (GitHub #702): an identifier becomes undefined       *)
(* inside an UNCHANGED expression during next-state computation.  The      *)
(* inner module x_unchanged declares a variable x that is replaced by the  *)
(* constant-valued operator fizzbuzz when it is instantiated, so the       *)
(* subformula UNCHANGED x becomes UNCHANGED fizzbuzz.                      *)
(***************************************************************************)

---------------------------- MODULE x_unchanged ----------------------------
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