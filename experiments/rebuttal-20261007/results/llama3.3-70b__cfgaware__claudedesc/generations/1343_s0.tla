---------------------------- MODULE TestModule ----------------------------
EXTENDS Integers

VARIABLE x, y

Init == (x = 0) /\ (y = 0) /\ (y = x)

Next ==[][UNCHANGED <<x, y>>]_<<x, y>>

Spec == Init /\ [][Next]_<<x, y>>
=============================================================================