------------------------------- MODULE SmallPlusCal -------------------------------

VARIABLES x, pc

CONSTANTS Init, Next, Spec

Init == /\ x \in 1..10
        /\ pc = "Start"

Next ==
    CASE pc = "Start" -> /\ x' = x
                         /\ pc' = "Done"
         [] pc = "Done" -> /\ x' = x
                          /\ pc' = pc

Spec == Init /\ [][Next]_<<x, pc>> /\ <>[](pc = "Done")

=============================================================================