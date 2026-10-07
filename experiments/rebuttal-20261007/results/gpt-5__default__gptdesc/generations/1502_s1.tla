------------------------------ MODULE SmallMachine ------------------------------

EXTENDS Naturals

CONSTANT Op(_)

VARIABLES x

Init == x = 0

Next == x' \in Op(x)

SubOfOp(S) == S \subseteq Op(x)

PowOp == SUBSET Op(x)

Spec == Init /\ [][Next]_x

============================================================================