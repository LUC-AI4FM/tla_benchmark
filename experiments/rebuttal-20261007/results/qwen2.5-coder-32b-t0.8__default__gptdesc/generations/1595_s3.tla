---- MODULE SequentialCounter ----
EXTENDS Integers, TLC

CONSTANTS MaxCount

VARIABLES x, pc

Init == /\ x = 0
        /\ pc = "Start"

Next ==
    \/ /\ pc = "Start"
       /\ x < MaxCount
       /\ x' = x + 1
       /\ pc' = "Loop"
    \/ /\ pc = "Loop"
       /\ x < MaxCount
       /\ x' = x + 1
       /\ pc' = "Loop"
    \/ /\ pc = "Loop"
       /\ x >= MaxCount
       /\ x' = x
       /\ pc' = "Done"

Spec ==
    /\ Init
    /\ [][Next]_<<pc>>
    /\ WF_[Next]_<<pc>>

Termination == <>[](pc = "Done")

AtFive == (x = 5)

FinishLoop == (pc = "Done" /\ x >= MaxCount)

PossibleCounts ==
    LET counts == [n \in 0..MaxCount |-> {}]
        in TLCGetSet("StateConstraints", counts)
           = [n \in 0..MaxCount
              |-> IF n <= MaxCount THEN {s \in S_ <<pc, x>> : x = n}
                  ELSE {}]

====