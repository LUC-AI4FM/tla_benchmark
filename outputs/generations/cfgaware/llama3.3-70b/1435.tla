---------------------------- MODULE OneVariableSystem ----------------------------
EXTENDS Integers

CONSTANT None

VARIABLE x

Init == (x = 0)

Next == (x' = x)

Spec == Init /\ [][Next]_x

THEOREM Spec => []Init
=============================================================================