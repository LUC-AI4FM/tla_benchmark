------------------------------- MODULE ArithmeticAssertion -------------------------------
EXTENDS Integers

CONSTANTS 
    \* No constants needed for this simple example

VARIABLES x, pc

Init == /\ x \in 1..10
        /\ pc = "Lbl_1"

Next == \/ /\ pc = "Lbl_1"
             /\ x * x <= 100
             /\ pc' = "Done"
             /\ x' = x
         \/ /\ pc = "Done"
             /\ pc' = "Done"
             /\ x' = x

Spec == Init /\ [][Next]_<<x, pc>>

Termination == <>[](pc = "Done")

=============================================================================