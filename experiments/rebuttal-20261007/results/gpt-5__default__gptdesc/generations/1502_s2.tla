--------------------------- MODULE SmallMachine ---------------------------

EXTENDS Naturals

CONSTANT Op(_)
VARIABLES x

Init == x = 0

Next == x' \in Op(x)

IsSubset(A, B) == A \subseteq B
Power(S) == SUBSET S

Spec == Init /\ [][Next]_x

============================================================================