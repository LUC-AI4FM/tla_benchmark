--------------------------- MODULE SmallSM ----------------------------
EXTENDS Naturals, Integers
CONSTANTS Op

VARIABLE x

Init == (x = 0)

Next == x' \in Op[x]

Spec == Init /\ [][Next]_x

SubsetHelper1(x) == {n \in Nat : n <= x} SUBSET {m \in Nat : m < 10}

SubsetHelper2(y) == {k \in Int : k = y} SUBSET Op[y]
===============================================================================