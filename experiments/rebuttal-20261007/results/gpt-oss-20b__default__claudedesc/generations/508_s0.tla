MODULE ArithmeticAssertion
EXTENDS Integers

VARIABLES x, pc

Init ==
    /\ x ∈ 1..10
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ x*x <= 100
    /\ pc' = "Done"
    /\ UNCHANGED x

Terminating ==
    /\ pc = "Done"
    /\ pc' = "Done"
    /\ UNCHANGED x

Next == Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_<<x,pc>>

Safety == x*x <= 100
Liveness == <> (pc = "Done")