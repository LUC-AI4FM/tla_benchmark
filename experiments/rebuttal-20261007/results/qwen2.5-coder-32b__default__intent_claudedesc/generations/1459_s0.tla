------------------------------- MODULE CounterSystem -------------------------------
EXTENDS Naturals

CONSTANTS UpperBound

VARIABLES counter

Init == counter = 0

Next ==
    \/ /\ counter < UpperBound
       /\ counter' = counter + 1
    \/ /\ counter >= UpperBound
       /\ counter' = counter

Spec ==
    /\ Init
    /\ [][Next]_<<counter>>

THEOREM Spec => []<>(counter = UpperBound)

=============================================================================