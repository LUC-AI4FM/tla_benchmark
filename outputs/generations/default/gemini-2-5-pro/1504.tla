---- MODULE TrivialStutter ----
EXTENDS TLC, Booleans

VARIABLES u1

vars == <<u1>>

Init == u1 = TRUE

Next == u1' = u1

Spec == Init /\ [][Next]_vars

Prop == ENABLED Next

=============================================================================