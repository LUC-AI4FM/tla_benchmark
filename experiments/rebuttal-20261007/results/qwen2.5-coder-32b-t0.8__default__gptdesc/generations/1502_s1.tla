---- MODULE SmallStateMachine ----
EXTENDS Naturals

CONSTANTS Op

VARIABLES x

Init == x = 0

Next == \E y \in Op(x) : x' = y

Spec == Init /\ [][Next]_<<x>>

SubsetOp ==
    \A s, t \in SUBSET NATURAL : s \subseteq t => (\A x \in s : Op(x) \subseteq t)

UnchangedOp ==
    \A x \in NATURAL : Op(Op(x)) = Op(x)
========================================