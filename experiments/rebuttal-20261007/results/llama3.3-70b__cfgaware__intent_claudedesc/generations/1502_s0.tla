---------------------------- MODULE HigherOrderConstantDemo ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Op, Forty2

VARIABLE x

Init == (x = 0)

Next == x' \in Op(x)

Spec == Init /\ [][Next]_x

THEOREM Spec => []<<x>>_x
=============================================================================