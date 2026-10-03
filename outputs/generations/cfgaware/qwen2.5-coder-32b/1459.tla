------------------------------- MODULE SmallTransitionSystem -------------------------------

CONSTANTS Limit

VARIABLES x

Init == x = 0

Next ==
    \/ /\ x < 3
       /\ x' = x + 1
    \/ /\ x >= 3
       /\ x' = x

Spec ==
    /\ Init
    /\ [][Next]_<<x>>

=============================================================================