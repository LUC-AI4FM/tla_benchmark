---------------------------- MODULE Specification ----------------------------

EXTENDS Naturals

VARIABLES x, y

Init == x = 0 /\ y = 0 /\ y = x

Next == UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_<<x, y>>

=============================================================================