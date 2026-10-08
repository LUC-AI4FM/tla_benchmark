------------------------------- MODULE StateConstraintPitfall -------------------------------
EXTENDS TLC, Integers

CONSTANTS MaxHistoryLength

VARIABLES state, history

Init == /\ state = "A"
        /\ history = << >>

Next ==
    \/ /\ state = "A"
       /\ state' = "B"
       /\ history' = Append(history, "A")
    \/ /\ state = "B"
       /\ state' = "A"
       /\ history' = Append(history, "B")

StateConstraint == Len(history) <= MaxHistoryLength

Spec ==
    /\ Init
    /\ [][Next]_<<state, history>>
    /\ WF_[Next]_<<state, history>>

LivenessProperty == <>[](state = "Done")

=============================================================================