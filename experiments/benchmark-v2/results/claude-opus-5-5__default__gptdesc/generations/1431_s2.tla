---- MODULE TwoStateHistory ----
EXTENDS Naturals, Sequences

CONSTANT MaxHistory

VARIABLES pc, history

vars == <<pc, history>>

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

TypeOK ==
    /\ pc \in {"A", "B"}
    /\ history \in Seq({"A"})

StateConstraint == Len(history) <= MaxHistory

Liveness == <>(pc = "Done")

====