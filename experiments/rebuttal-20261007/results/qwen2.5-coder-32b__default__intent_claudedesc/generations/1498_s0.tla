------------------------------- MODULE ToggleSystem -------------------------------
EXTENDS Naturals

CONSTANTS Action1, Action2

VARIABLES toggleState

Init == toggleState = FALSE

Next ==
  \/ /\ ACTION = Action1
     /\ toggleState' = ~toggleState
  \/ /\ ACTION = Action2
     /\ toggleState' = ~toggleState

Spec == Init /\ [][Next]_<<ACTION>>

=============================================================================