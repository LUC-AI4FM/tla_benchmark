------------------------------- MODULE TwoStateProcess -------------------------------
EXTENDS TLC, Sequences

CONSTANTS MaxHistoryLength

VARIABLES pc, history

Init == /\ pc = "A"
        /\ history = << >>

Next == \/ /\ pc = "A"
               /\ history' = Append(history, "A")
               /\ pc' = "B"
          \/ /\ pc = "B"
               /\ history' = history
               /\ pc' = "A"

Spec == Init /\ [][Next]_<<pc, history>> /\ WF_[Next]_<<pc, history>>

StateConstraint == Len(history) <= MaxHistoryLength

LivenessProperty == <>[](pc = "Done")

Invariant == StateConstraint

SpecWithInvariants == Spec /\ []Invariant

=============================================================================