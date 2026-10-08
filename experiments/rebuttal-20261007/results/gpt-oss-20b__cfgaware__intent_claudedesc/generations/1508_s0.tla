------------------------------ MODULE OneVarSM ------------------------------
EXTENDS Naturals

VARIABLE x

(* Initial condition *)
Init == x = 0

(* Next-state relation with stuttering closure *)
Next ==
    \/ (x' = x)                     (* stutter step *)
    \/ (x' = 5)
    \/ (x' ∈ {1,2})
    \/ (x' = 10)
    \/ /\ x = 0 /\ x' = 1
    \/ /\ x = 1 /\ x' = 2

(* Invariant: variable stays within a small bounded type and remains at its initial value zero *)
Inv == (x ∈ {0,1,2}) /\ (x = 0)

(* Specification: initial condition, closed next-state relation, invariant *)
Spec == Init /\ [][Next]_x /\ Inv

===============================================================================