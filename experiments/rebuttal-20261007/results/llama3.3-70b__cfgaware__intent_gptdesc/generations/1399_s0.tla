---------------------------- MODULE ToggleSystem ----------------------------
EXTENDS Integers, TLC

CONSTANT None

VARIABLE state

Prop == [](state = TRUE \/ state = FALSE)

Spec == 
  (state = TRUE) /\ 
  [](state' = ~state \/ state' = state)

THEOREM Spec => []Prop
=============================================================================