------------------------------- MODULE CounterSystem -------------------------------

CONSTANTS Limit

VARIABLES counter

Init == counter = 0

Next ==
    \/ /\ counter < Limit
       /\ counter' = counter + 1
    \/ /\ counter >= Limit
       /\ counter' = counter

Spec == Init /\ [][Next]_<<counter>>

=============================================================================