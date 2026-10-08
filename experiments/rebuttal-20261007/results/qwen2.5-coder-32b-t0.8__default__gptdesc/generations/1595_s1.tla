---- MODULE SequentialCounter ----

EXTENDS Naturals, Sequences, TLC

CONSTANTS MaxCount

VARIABLES x, pc

Init == /\ x = 0
        /\ pc = "Start"

Next == \/ /\ pc = "Start"
             /\ x < MaxCount
             /\ x' = x + 1
             /\ pc' = "Loop"
          \/ /\ pc = "Loop"
             /\ x < MaxCount
             /\ x' = x + 1
             /\ pc' = "Loop"
          \/ /\ pc = "Loop"
             /\ x >= MaxCount
             /\ pc' = "Done"

Spec == Init /\ [][Next]_<<pc>> /\ WF_[Next]_<<pc>>

Termination == <>[](pc = "Done")

AtFive == x = 5

FinishLoop == x >= MaxCount

PossibleCounts ==
    \E s \in StateTrace : 
        /\ Len(StatesThatSatisfy(s, AtFive)) > 0
        /\ Len(StatesThatSatisfy(s, FinishLoop)) > 0

====