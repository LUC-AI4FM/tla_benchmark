------------------------------- MODULE SmallStateMachine -------------------------------
EXTENDS Naturals

CONSTANTS Op

VARIABLES x

Init == x = 0

Next == \E val \in Op(x) : x' = val

Spec == Init /\ [][Next]_<<x>>

Invariants ==
    UNCHANGED << >>

LivenessProperties ==
    TRUE
=============================================================================