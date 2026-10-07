----------------------------- MODULE SmallMachine -----------------------------

EXTENDS Naturals

CONSTANT Op(_)

VARIABLES x

Init == x = 0

Next == x' \in Op(x)

IsSubset(S, T) == S \subseteq T

IsSubsetOfOp(S) == S \subseteq Op(x)

Spec == Init /\ [][Next]_x

=============================================================================