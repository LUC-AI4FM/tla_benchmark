----------------------------- MODULE IncrementToFive -----------------------------

EXTENDS Naturals

CONSTANTS MaxValue

VARIABLES x

Init == x = 1

Next ==
    \/ /\ x < MaxValue
       /\ x' = x + 1
    \/ /\ x = MaxValue
       /\ x' = x

Spec ==
    /\ Init
    /\ [][Next]_<<x>>
    /\ WF_<<x>>(Next)

\* Liveness: From the initial value x = 1, the system eventually reaches and thereafter always remains at x = 5.
Live == <>[](x = MaxValue)

=============================================================================