---- MODULE TwoStateProcess ----
EXTENDS TLC, Naturals, Sequences

CONSTANT MaxHistoryLen

VARIABLES pc, history

vars == <<pc, history>>

Init ==
    /\ pc = "A"
    /\ history = <<>>

A ==
    /\ pc = "A"
    /\ pc' = "B"
    /\ history' = Append(history, "A")

B ==
    /\ pc = "B"
    /\ pc' = "A"
    /\ history' = history

Next == A \/ B

Spec == Init /\ [][Next]_vars /\ WF_vars(A \/ B)

StateConstraint == Len(history) <= MaxHistoryLen

Liveness == <>(pc = "Done")

================================