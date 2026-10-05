---------------------------- MODULE Trivial ----------------------------
VARIABLES u1

vars == <<u1>>

Init == u1 = TRUE

Next == UNCHANGED <<u1>>

Prop == ENABLED Next
=========================================================================