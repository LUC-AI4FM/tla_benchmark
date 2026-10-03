------------------------------- MODULE TwoState --------------------------------

EXTENDS Naturals, Sequences

CONSTANT MaxLen

VARIABLES pc, history

vars == << pc, history >>

Init ==
  /\ pc = "A"
  /\ history = << >>

A ==
  /\ pc = "A"
  /\ pc' = "B"
  /\ history' = Append(history, pc)

B ==
  /\ pc = "B"
  /\ pc' = "A"
  /\ history' = history

Next == A \/ B

Spec ==
  /\ Init
  /\ [][A \/ B]_vars
  /\ WF_vars(A \/ B)

StateConstraint == Len(history) <= MaxLen

Liveness == <> (pc = "Done")

===============================================================================