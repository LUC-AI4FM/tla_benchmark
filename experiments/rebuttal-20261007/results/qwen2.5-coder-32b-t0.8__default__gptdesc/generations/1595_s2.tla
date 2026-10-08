```tla
MODULE SequentialCounter

EXTENDS Naturals, Sequences, TLC

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

Spec ==
    /\ Init
    /\ [][Next]_<<x, pc>>
    /\ WF_[Next]_<<x, pc>>

Termination == <>[]<>(pc = "Done")

AtFive == (x = 5)

FinishLoop == (x >= MaxCount)

PossibleCounts ==
    /\ AtFive => <<x>> \in TLCGet("StateConstraints", "SequentialCounter", "AtFive")
    /\ FinishLoop => <<x>> \in TLCGet("StateConstraints", "SequentialCounter", "FinishLoop")

```