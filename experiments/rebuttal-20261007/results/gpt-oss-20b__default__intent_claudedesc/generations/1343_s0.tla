MODULE ConjunctiveInit

EXTENDS Naturals, TLC

VARIABLES x, y

(* --- Initialization --- *)
Init ==
    /\ y = 0
    /\ x = 0
    /\ y = x

(* --- Next-state relation (stuttering) --- *)
Next == UNCHANGED <<x, y>>

(* --- Specification --- *)
Spec == Init /\ [][Next]_<<x, y>>

(* --- Invariant that the system stays at (0,0) --- *)
Inv == (x = 0 /\ y = 0)

THEOREM Spec_Imply_Inv == Spec => []Inv

===============================================================================