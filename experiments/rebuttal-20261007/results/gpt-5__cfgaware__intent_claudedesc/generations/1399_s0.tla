------------------------------ MODULE ToggleBool ------------------------------

VARIABLE b

(*
  A single Boolean variable that toggles between TRUE and FALSE on every step.
  Initial state: b = TRUE
  Transition: flips b each step (no stuttering allowed).
*)

Init == b = TRUE

Next == b' = ~b

Spec == Init /\ []Next

(*
  Property under test (intentionally violated):
  "b is always TRUE" — falsified by the first step, since b toggles to FALSE.
*)
Prop == [](b = TRUE)

(*
  Additional properties for experimentation:
  - A state predicate asserting b = TRUE.
  - A trivially true temporal property.
  - The variable exposed directly as a property (state predicate).
*)
IsTrueState == b = TRUE
TrivialAlways == []TRUE
ExposeVar == b

=============================================================================