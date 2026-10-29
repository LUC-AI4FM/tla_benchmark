---- MODULE SmallStateSpace ----
EXTENDS Naturals, TLC

VARIABLE x

Init == /\ Print("Starting: exploring functions [1..6 -> 1..7]", TRUE)
        /\ x \in [1..6 -> 1..7]

Next == UNCHANGED x

Inv == TRUE

Spec == Init /\ [][Next]_x
====