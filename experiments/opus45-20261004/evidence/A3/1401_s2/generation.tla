---------------------------- MODULE InnerCounter ----------------------------
VARIABLE x

TypeOK == x \in 0..3

Init == x = 0

Step == x < 3 /\ x' = x + 1

Next == Step \/ (x >= 3 /\ UNCHANGED x)

Spec == Init /\ [][Next]_x /\ WF_x(Step)

EventuallyThree == <>(x = 3)

=============================================================================