---------------------------- MODULE Spec ----------------------------

VARIABLES u1

vars == <<u1>>

Init == u1 = TRUE

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

Prop == ENABLED Next

TypeInvariant == u1 \in BOOLEAN

=========================================================================