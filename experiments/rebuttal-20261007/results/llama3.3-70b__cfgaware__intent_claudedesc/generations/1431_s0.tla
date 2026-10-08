---------------------------- MODULE StateConstraintPitfall ----------------------------
EXTENDS Integers

CONSTANT MaxHistory
VARIABLE history, state

Init == (history = <<>>) /\ (state = "A")

Next == SF_VARIABLES /\ 
        ((state = "A") => (state' = "B") /\ (history' = Append(history, "A"))) \*
        ((state = "B") => (state' = "A") /\ (history' = Append(history, "B")))

Spec == Init /\ [][Next]_<<state, history>>
HistoryConstraint == Len(history) <= MaxHistory
LivenessProperty == <>[]((state = "Done"))

THEOREM Spec => []<>LivenessProperty
=============================================================================