------------------------------------------- MODULE BoolStateMachine -------------------------------------------
EXTENDS Naturals, TLC

VARIABLES x

(* --- Initial condition ------------------------------------------------------------ *)
Init == x = TRUE

(* --- Next-state relation: flip the boolean value --------------------------------- *)
Next == x' = ~x

(* --- Stuttering step (no change) ------------------------------------------------- *)
Stutter == x' = x

(* --- State predicates (simple examples) ------------------------------------------ *)
XTrue  == x = TRUE
XFalse == x = FALSE

(* --- Specification: initial condition and every step is either Next or stutter ---- *)
Spec == Init /\ [] (Next \/ Stutter)

=============================================================================