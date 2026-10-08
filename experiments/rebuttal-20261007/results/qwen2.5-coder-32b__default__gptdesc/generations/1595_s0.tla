------------------------------- MODULE SequentialCounter -------------------------------
EXTENDS Naturals, TLC

CONSTANTS MaxCount

VARIABLES x, pc

Init == /\ x = 0
        /\ pc = "Start"

Next == \/ /\ pc = "Start"
             /\ x < MaxCount
             /\ x' = x + 1
             /\ pc' = "Start"
          \/ /\ pc = "Start"
             /\ x >= MaxCount
             /\ pc' = "Done"

Spec == Init /\ [][Next]_<<pc>>

Fairness == WF_next(Next)

Termination == <>[](pc = "Done")

AtFive == (x = 5)

FinishLoop == (pc = "Done" /\ x = MaxCount)

PossibleCounts ==
    LET counts == [n \in 0..MaxCount |-> TLCGet("StateConstraint", n)]
    IN  /\ counts[0] > 0
        /\ counts[MaxCount] > 0

=============================================================================