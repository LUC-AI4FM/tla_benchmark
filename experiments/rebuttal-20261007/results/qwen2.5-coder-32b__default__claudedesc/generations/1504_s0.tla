------------------------------- MODULE G -----------------------------------

EXTENDS TLC, SpecifyingSystems

CONSTANTS vars

VARIABLES u1

Init == u1 = TRUE

Next == UNCHANGED vars /\ UNCHANGED <<u1>> /\ UNCHANGED u1

Spec == Init /\ [][Next]_<<u1>>

Prop == ENABLED Next

=============================================================================