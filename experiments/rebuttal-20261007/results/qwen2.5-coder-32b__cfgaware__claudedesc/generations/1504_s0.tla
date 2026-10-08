---- MODULE G ----

VARIABLE u1

CONSTANTS vars

Init == u1 = TRUE

Next == UNCHANGED vars /\ UNCHANGED <<u1>> /\ UNCHANGED u1

Prop == ENABLED Next

====