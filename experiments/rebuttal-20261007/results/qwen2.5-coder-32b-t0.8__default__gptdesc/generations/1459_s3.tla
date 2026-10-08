------------------------------- MODULE SmallTransitionSystem -------------------------------
EXTENDS Naturals

CONSTANTS 
    -- No constants defined in this specification

VARIABLES 
    x

Init == x = 0

Next ==
    \/ /\ x < 3
       /\ x' = x + 1
    \/ /\ x >= 3
       /\ x' = x

Spec ==
    Init /\ [][Next]_<<x>>

=============================================================================