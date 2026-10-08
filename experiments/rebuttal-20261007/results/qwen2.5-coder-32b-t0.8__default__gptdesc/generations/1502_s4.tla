------------------------------- MODULE SmallStateMachine -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Op

VARIABLES x

Init == x = 0

Next == /\ \/ \E v \in (Op(x)) : x' = v
         /\ UNCHANGED << >>

Spec == Init /\ [][Next]_<<x>>

=============================================================================