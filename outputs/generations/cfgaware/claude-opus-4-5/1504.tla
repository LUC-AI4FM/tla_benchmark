---------------------------- MODULE Specification ----------------------------

VARIABLE u1

vars == <<u1>>

Init == u1 = TRUE

Next == UNCHANGED vars

Prop == ENABLED Next

=============================================================================