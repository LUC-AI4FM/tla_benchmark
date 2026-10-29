---- MODULE TwoStateHistory ----
EXTENDS Naturals, Sequences

CONSTANT MaxHistory

VARIABLES pc, history

vars == <<pc, history>>

TypeOK ==
    /\ pc \in {"A", "B", "Done"}
    /\ history \in Seq({"A", "B", "Done"})

Init ==
    /\ pc = "A"
    /\ history = <<>>

A ==
    /\ pc = "A"
    /\ pc' = "B"
    /\ history' = Append(history, pc)

B ==
    /\ pc = "B"
    /\ pc' = "A"
    /\ UNCHANGED history

Next == A \/ B

Spec == Init /\ [][A \/ B]_vars /\ WF_vars(A \/ B)

StateConstraint == Len(history) <= MaxHistory

Liveness == <>(pc = "Done")

====