---------------------------- MODULE Github702 ----------------------------
(***************************************************************************)
(* Models a TLC issue (GitHub #702) in which an identifier became          *)
(* undefined inside an UNCHANGED expression while computing next states.   *)
(* The instantiated module x_unchanged asserts UNCHANGED <<x, z>>. Here x  *)
(* is replaced by the constant-valued operator fizzbuzz through the        *)
(* INSTANCE substitution x <- fizzbuzz. TLC must evaluate fizzbuzz         *)
(* correctly inside the UNCHANGED expression, instead of reporting it as   *)
(* undefined.                                                              *)
(***************************************************************************)

    ---------------------------- MODULE x_unchanged ----------------------------
    EXTENDS Naturals

    VARIABLES x, y, z

    vars == <<x, y, z>>

    Init ==
        /\ x \in {1, 2, 3}
        /\ y \in {1, 2, 3}
        /\ z \in {1, 2, 3}

    Next ==
        /\ y' = y + 1
        /\ UNCHANGED <<x, z>>

    Spec == Init /\ [][Next]_<<x, y, z>>
    ============================================================================