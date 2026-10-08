MODULE SmallSM
EXTENDS Naturals

CONSTANT Op

VARIABLE x

Init == x = 0

Next == /\ x' \in Op(x)

Helper1(a) == a \subseteq Op(x)
Helper2(b) == Op(x) \subseteq b

Spec == Init /\ [][Next]_x