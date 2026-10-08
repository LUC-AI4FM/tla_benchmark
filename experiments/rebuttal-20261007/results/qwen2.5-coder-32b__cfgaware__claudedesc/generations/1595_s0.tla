------------------------------- MODULE SequentialCounter -------------------------------

VARIABLES x, pc

CONSTANTS Lbl_1, Done

Lbl_1 == "Lbl_1"
Done  == "Done"

Init == /\ x = 0
        /\ pc = Lbl_1

Next ==
    \/ /\ pc = Lbl_1
       /\ x < 10
       /\ x' = x + 1
       /\ pc' = Lbl_1
    \/ /\ pc = Lbl_1
       /\ x >= 10
       /\ pc' = Done

Terminating ==
    /\ pc = Done
    /\ x' = x
    /\ pc' = pc

Spec ==
    /\ Init
    /\ [][Next \/ Terminating]_<<x, pc>>
    /\ WF_[Next]_<<x, pc>>

Termination == <>[](pc = Done)

AtFive == (x = 5)
FinishLoop == (x = 9) /\ (pc' = Done)

PossibleCounts ==
    /\ TLCGet("States") \subseteq {s \in TLCGet("StateSpace") : AtFive(s)}
    /\ TLCGet("States") \subseteq {s \in TLCGet("StateSpace") : FinishLoop(s)}
    /\ Cardinality({s \in TLCGet("States") : AtFive(s)}) = 1
    /\ Cardinality({s \in TLCGet("States") : FinishLoop(s)}) = 1

=============================================================================