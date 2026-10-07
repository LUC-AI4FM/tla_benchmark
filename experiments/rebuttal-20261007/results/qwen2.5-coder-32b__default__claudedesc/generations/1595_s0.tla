------------------------------- MODULE SequentialCounter -------------------------------
EXTENDS Integers, TLC

CONSTANTS 
    \* No constants needed for this simple example

VARIABLES x, pc

Init == /\ x = 0
        /\ pc = "Lbl_1"

Next == \/ /\ pc = "Lbl_1"
             /\ x < 10
             /\ x' = x + 1
             /\ pc' = "Lbl_1"
          \/ /\ pc = "Lbl_1"
             /\ x >= 10
             /\ pc' = "Done"
          \/ /\ pc = "Done"
             /\ x' = x
             /\ pc' = "Done"

Spec == Init /\ [][Next]_<<pc>>

Termination == <>[](pc = "Done")

AtFive == (x = 5)
FinishLoop == (x = 9) /\ (pc = "Lbl_1")

PossibleCounts ==
    /\ _TE<><>(AtFive)
    /\ _TE<><>(FinishLoop)

=============================================================================