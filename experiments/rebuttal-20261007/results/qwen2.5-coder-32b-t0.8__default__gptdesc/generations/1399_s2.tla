------------------------------- MODULE BooleanStateMachine -------------------------------
EXTENDS TLC

CONSTANTS x0

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec == 
  /\ Init
  /\ [][Next \/ UNCHANGED x]_<<x>>

=============================================================================