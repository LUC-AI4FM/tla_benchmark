------------------------------- MODULE PositiveVariable -------------------------------

EXTENDS Integers, TLC

CONSTANTS Domain

VARIABLES x

Init == x = 23

Next ==
    \/ /\ x' \in {0, 1}
       /\ x' > 0
    \/ x' = x

Spec ==
    /\ Init
    /\ [][Next]_<<x>>

Inv ==
    x > 0

SpecWithInvariants ==
    Spec /\ Inv

=============================================================================