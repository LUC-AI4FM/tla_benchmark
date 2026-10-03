---------------------------- MODULE Specification ----------------------------

VARIABLES u1

vars == <<u1>>

Init == u1 = TRUE

Next == UNCHANGED <<u1>>

Spec == Init /\ [][Next]_vars

Prop == ENABLED Next

=============================================================================