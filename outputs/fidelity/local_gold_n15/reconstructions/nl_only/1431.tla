---- MODULE TwoStateProcess ----

EXTENDS Naturals, Sequences, TLC

CONSTANTS MaxHistoryLength

VARIABLES pc, history

Init == /\ pc = "A"
        /\ history = << >>

Next ==
    \/ /\ pc = "A"
       /\ history' = Append(history, "A")
       /\ pc' = "B"
    \/ /\ pc = "B"
       /\ history' = history
       /\ pc' = "A"

StateConstraint == Len(history) <= MaxHistoryLength

Spec ==
    /\ Init
    /\ [][Next]_<<pc, history>>
    /\ WF_[Next]_<<pc, history>>
    /\ StateConstraint
    /\ [](<>[pc = "Done"]_<<pc, history>>)

DONE == pc = "Done"
========================================