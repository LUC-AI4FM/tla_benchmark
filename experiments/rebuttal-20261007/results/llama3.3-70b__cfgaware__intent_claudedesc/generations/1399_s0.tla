---------------------------- MODULE SimpleToggle ----------------------------
EXTENDS Integers

CONSTANT None

VARIABLE toggle

Init == (toggle = TRUE)

Next == (toggle' = ~toggle)

Spec == Init /\ [][Next]_toggle

Prop == 
  <<
    "AlwaysTrue" : [](toggle = TRUE)
  ; "EqualsTrue" : (toggle = TRUE)
  ; "TriviallyTrue" : TRUE
  ; "ToggleValue" : toggle
  >>

=============================================================================