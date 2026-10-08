MODULE SmallSM
EXTENDS Integers

CONSTANT Op

VARIABLES x

Init == x = 0

Next == x' \in Op(x)

helper1(a) == a \subseteq {0, 1}

helper2(b) == b \subseteq Op(0)

Spec == Init /\ [][Next]_x