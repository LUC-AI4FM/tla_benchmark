------------------------------- MODULE BooleanStateMachine -------------------------------

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec ==
  /\ Init
  /\ [][Next \/ UNCHANGED x]_<<x>>

Prop ==
  /\ []Init
  /\ [](Next \/ UNCHANGED x)

=============================================================================