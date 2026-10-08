------------------------------- MODULE SmallTransitionSystem -------------------------------
EXTENDS Naturals

CONSTANTS MaxValue

VARIABLES x

Init == x = 0

Next ==
    \/ /\ x < MaxValue
       /\ x' = x + 1
    \/ /\ x >= MaxValue
       /\ x' = x

Spec ==
    /\ Init
    /\ [](Init \/ [][Next]_<<x>>)

=============================================================================