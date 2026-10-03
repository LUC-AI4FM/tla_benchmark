------------------------------ MODULE TrivialStutter ------------------------------
VARIABLES x, y

(* --- Initial state predicate --- *)
Init == /\ x = 0
        /\ y = 0
        /\ (x = y)

(* --- Next-state relation (stuttering) --- *)
Next == /\ x' = x
        /\ y' = y

(* --- Temporal specification: initial state and stuttering forever --- *)
Spec == Init /\ []Next

=============================================================================