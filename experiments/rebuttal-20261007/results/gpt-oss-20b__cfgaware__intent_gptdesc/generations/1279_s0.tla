------------------------------ MODULE SimpleVar ------------------------------
EXTENDS Naturals, TLC

(*--------------------------------------------------------------------------*)
(* CONSTANTS
   AllowedValues : finite set of integers from which the variable may be
                   reassigned (must contain only positive values).
   InitVal      : concrete integer that initializes the variable.
*)
CONSTANTS AllowedValues, InitVal

(*--------------------------------------------------------------------------*)
(* VARIABLES *)
VARIABLE x

(*--------------------------------------------------------------------------*)
(* INITIAL STATE *)
Init == 
  /\ x = InitVal

(*--------------------------------------------------------------------------*)
(* TRANSITION RELATION
   The system may either stutter (x' = x) or assign a new value that is
   chosen nondeterministically from AllowedValues and strictly positive.
*)
Next ==
  \/ x' = x                                 (* stuttering step *)
  \/ /\ x' \in AllowedValues
      /\ x' > 0

(*--------------------------------------------------------------------------*)
(* SAFETY INVARIANT: the variable is never zero. *)
Inv == 
  x /= 0

(*--------------------------------------------------------------------------*)
(* TEMPORAL PROPERTY: every transition respects the allowed-value constraint.
   This property holds for all steps, including stuttering steps.
*)
TransConstraint ==
  [] (Next => (x' = x) \/ (x' \in AllowedValues /\ x'>0))

(*--------------------------------------------------------------------------*)
(* SPECIFICATION *)
Spec == 
  Init /\ [][Next]_x

(*--------------------------------------------------------------------------*)
(* PROPERTIES TO BE CHECKED *)
Safety   == Inv
Liveness == TransConstraint

=============================================================================