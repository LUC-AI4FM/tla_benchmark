------------------------------ MODULE Toggle ------------------------------
EXTENDS TLC

VARIABLE b

(* --- Initialization ----------------------------------------------------- *)
Init == b = TRUE

(* --- Next-state relation ----------------------------------------------- *)
Next == b' = NOT b

(* --- Specification ------------------------------------------------------ *)
Spec == Init /\ [][Next]_<<b>>

(* --- Property to be checked (intentionally violated) ------------------- *)
Prop == [] (b = TRUE)

(* ------------------------------------------------------------------------ *)

(* Additional properties for experimentation: *)
StatePredicate == b = TRUE
TrivialProperty  == TRUE
ExposeVar        == b

=============================================================================