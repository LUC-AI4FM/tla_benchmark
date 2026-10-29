---------------------------- MODULE Github702 ----------------------------
(***************************************************************************)
(* Models a TLC issue (GitHub #702): an identifier becomes undefined       *)
(* inside an UNCHANGED expression during next-state computation. The       *)
(* variable x of module x_unchanged is replaced by the constant-valued     *)
(* operator fizzbuzz. As a result, "UNCHANGED <<x, y, z>>" in the          *)
(* instantiated module refers to fizzbuzz, which is not a state variable.  *)
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
    =============================================================================