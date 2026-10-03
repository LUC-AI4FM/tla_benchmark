----------------------------- MODULE OneVarStutter -----------------------------
EXTENDS Naturals

CONSTANTS DummyConst

VARIABLES x

Init == x = 0

Next == UNCHANGED x

Spec == Init /\ []Next
=============================================================================