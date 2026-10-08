------------------------------ MODULE ConjInit ------------------------------
EXTENDS Naturals

VARIABLES x, y

(* --- Initial state constraints ------------------------------------------- *)
Init == /\ y = 0
        /\ x = 0
        /\ y = x

(* --- Next-state relation (variables stay unchanged) --------------------- *)
Next == UNCHANGED <<x, y>>

(* --- Complete specification ---------------------------------------------- *)
Spec == Init /\ [][Next]_<<x, y>>

(* --- Theorems ----------------------------------------------------------- *)

THEOREM OnlyZeroState ==
    Spec => [](x = 0 /\ y = 0)

THEOREM StutterClosedSafety ==
    Spec => []Next

END ConjInit