------------------------------- MODULE ArithmeticAssertion -------------------------------

VARIABLES x, pc

CONSTANTS InitXValues == 1..10

Init == /\ x \in InitXValues
        /\ pc = "Lbl_1"

Next ==
    \/ /\ pc = "Lbl_1"
       /\ x * x <= 100
       /\ pc' = "Done"
       /\ x' = x
    \/ /\ pc = "Done"
       /\ pc' = "Done"
       /\ x' = x

Spec == Init /\ [][Next]_<<x, pc>>

Termination == <>(pc = "Done")

=============================================================================