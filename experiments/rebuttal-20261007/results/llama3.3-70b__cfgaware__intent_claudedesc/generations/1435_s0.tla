---------------------------- MODULE MinimalSpec ----------------------------
EXTENDS Integers

VARIABLE x

Init == (x = 0)

Next == (x' = x)

Spec == Init /\ [][Next]_x

THEOREM Spec => [](x = 0)
=============================================================================