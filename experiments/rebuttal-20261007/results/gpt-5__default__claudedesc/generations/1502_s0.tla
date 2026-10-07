------------------------------- MODULE MinimalOp -------------------------------
EXTENDS Naturals

CONSTANT Op

VARIABLE x

Id(n) == SUBSET {1, 2, 3}
Forty2(n) == Id(n)

Init == x = 0

Next == x' \in Op(x)

Spec == Init /\ [][Next]_x
================================