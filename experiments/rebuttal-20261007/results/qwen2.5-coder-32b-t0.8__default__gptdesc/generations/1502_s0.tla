------------------------------- MODULE SmallStateMachine -------------------------------
EXTENDS Naturals

CONSTANTS Op

VARIABLES x

Init == x = 0

Next == /\ \/ x' \in Op(x)
         /\ UNCHANGED << >>

Spec == Init /\ [][Next]_<<x>>

SubsetHelper(S) == S \subseteq (DOMAIN Op)

ValueHelper(v) == v \in DOMAIN Op
================================================================================