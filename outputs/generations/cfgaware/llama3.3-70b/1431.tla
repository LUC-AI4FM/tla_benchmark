---------------------------- MODULE TwoStateProcess ----------------------------
EXTENDS Integers, Sequences

CONSTANT Done
VARIABLE pc, history

Init == (pc = "A") /\ (history = <<>>)

Next_A == (pc' = "B") /\ (history' = Append(history, pc)) /\ (pc = "A")
Next_B == (pc' = "A") /\ (history' = history) /\ (pc = "B")

Next == Next_A \/ Next_B

Spec == Init /\ [][Next]_<<pc, history>> /\ WF_<<pc, history>>(Next_A \/ Next_B)

HistoryConstraint == Len(history) <= 5

Liveness == <> (pc = "Done")

THEOREM Spec => [] HistoryConstraint
THEOREM Spec => Liveness
=============================================================================