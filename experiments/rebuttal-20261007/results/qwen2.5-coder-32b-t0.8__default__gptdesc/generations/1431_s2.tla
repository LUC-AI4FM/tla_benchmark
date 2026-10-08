------------------------------- MODULE TwoStateProcess -------------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS MaxHistoryLength

VARIABLES pc, history

Init == 
    /\ pc = "A"
    /\ history = <<>>

Next ==
    \/ /\ pc = "A"
       /\ history' = Append(history, "A")
       /\ pc' = "B"
    \/ /\ pc = "B"
       /\ history' = history
       /\ pc' = "A"

Spec == 
    Init /\ [][Next]_<<pc, history>> /\ WF_[Next]_<<pc, history>>

StateConstraint ==
    Len(history) <= MaxHistoryLength

Liveness ==
    <>[]<>(pc = "Done")

SpecWithConstraints ==
    Spec /\ StateConstraint /\ Liveness

=============================================================================