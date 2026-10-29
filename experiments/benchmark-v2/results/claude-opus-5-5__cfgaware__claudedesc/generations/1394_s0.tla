------------------------------ MODULE Github702 ------------------------------
(***************************************************************************)
(* Regression test: TLC must correctly handle an UNCHANGED expression when *)
(* a variable of the instantiated module is substituted by a defined       *)
(* operator (rather than a variable) in the instantiating module.          *)
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
    ============================================================================