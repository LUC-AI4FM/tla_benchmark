---------------------------- MODULE Inner ----------------------------
VARIABLE x

Init == x = 0

Step == x < 3 /\ x' = x + 1

Next == Step

Fairness == WF_x(Step)

Spec == Init /\ [][Next]_x /\ Fairness

Prop == <>(x = 3)

=======================================================================