------------------------------ MODULE ConstraintLivenessWarning ------------------------------

EXTENDS Sequences

CONSTANTS DummyConst

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

Act == A \/ B

Next == Act

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Act)

Constraint == Len(history) < 3

Prop == <> (pc = "Done")

=============================================================================