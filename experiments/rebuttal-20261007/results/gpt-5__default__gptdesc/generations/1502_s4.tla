---- MODULE SmallStateMachine ----
EXTENDS Naturals

CONSTANT Op

VARIABLES x

Init == x = 0

Next == x' \in Op(x)

SubsetEq(S, T) == S \subseteq T

ProperSubset(S, T) == S \subset T

Spec == Init /\ [][Next]_x
====