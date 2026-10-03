------------------------------- MODULE IncrementToFive -------------------------------

VARIABLES x

CONSTANTS Init, Next, Spec, Liveness

Init == x = 1

Next ==
    \/ /\ x < 5
       /\ x' = x + 1
    \/ /\ x = 5
       /\ x' = x

Spec ==
    /\ Init
    /\ [][Next]_<<x>>

Liveness ==
    <>[](x = 5)

=============================================================================