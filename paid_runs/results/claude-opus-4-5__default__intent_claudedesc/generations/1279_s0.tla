---------------------------- MODULE ConjunctiveConstraint ----------------------------
EXTENDS Integers

VARIABLES x

Init == x = 23

Next ==
    \E v \in {0, 1} :
        /\ v > 0
        /\ x' = v

Spec == Init /\ [][Next]_x

NeverZero == x /= 0

===================================================================================