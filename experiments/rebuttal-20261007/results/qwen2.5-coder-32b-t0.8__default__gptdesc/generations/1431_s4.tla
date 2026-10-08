------------------------------- MODULE TwoStateProcess -------------------------------
EXTENDS Integers, Sequences

CONSTANTS MaxHistoryLength

VARIABLES pc, history

Init == /\ pc = "A"
        /\ history = << >>

Next ==
    \/  /\ pc = "A"
        /\ history' = Append(history, "A")
        /\ pc' = "B"
    \/  /\ pc = "B"
        /\ history' = history
        /\ pc' = "A"

Spec == Init /\ [][Next]_<<pc, history>> /\ WF_[Next]_<<pc, history>>

StateConstraint ==
    Len(history) <= MaxHistoryLength

LivenessProperty ==
    <>[](pc = "Done")

TemporalProperties ==
    StateConstraint /\ LivenessProperty

CompleteSpec == Spec /\ TemporalProperties
=============================================================================