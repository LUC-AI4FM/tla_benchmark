------------------------------ MODULE ToggleSystem ------------------------------
VARIABLES b

Init == 
  /\ b = FALSE

Action1 ==
  /\ b' = \lnot b

Action2 ==
  /\ b' = \lnot b

Next == Action1 \/ Action2

Spec == Init /\ [][Next]_b
=============================================================================