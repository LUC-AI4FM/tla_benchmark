---------------------------- MODULE Specification ----------------------------

EXTENDS Sequences, Naturals

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
    /\ history' = history

Next == A \/ B

Spec == Init /\ [][Next]_vars /\ WF_vars(A \/ B)

StateConstraint == Len(history) <= 10

Liveness == <>(pc = "Done")

=============================================================================