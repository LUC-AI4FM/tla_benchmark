---- MODULE TwoStateWithHistory ----
EXTENDS Sequences, Naturals

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
  /\ UNCHANGED history

Next == A \/ B

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

StateConstraint == Len(history) <= MaxLen

EventuallyDone == <> (pc = "Done")

====