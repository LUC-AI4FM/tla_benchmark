------------------------------- MODULE PositiveVariable -------------------------------

VARIABLES x

CONSTANTS Init, Next, Spec, Inv

Init == x = 23

Next ==
    \/ /\ x' \in {0, 1}
       /\ x' > 0
    \/ x' = x

Spec == Init /\ [][Next]_<<x>>

Inv == x > 0

=============================================================================