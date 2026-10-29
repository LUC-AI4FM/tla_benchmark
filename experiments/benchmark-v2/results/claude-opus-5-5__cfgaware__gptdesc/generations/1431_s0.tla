---------------------------- MODULE TwoStateHistory ----------------------------
EXTENDS Naturals, Sequences

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

Spec ==
    /\ Init
    /\ [][A \/ B]_vars
    /\ WF_vars(A \/ B)

Constraint == Len(history) < 3

Prop == <>(pc = "Done")

=============================================================================