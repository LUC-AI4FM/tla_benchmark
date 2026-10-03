----------------------------- MODULE TwoStateHistory -----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANT MaxLen
ASSUME MaxLen \in Nat

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
  /\ [][Next]_vars
  /\ WF_vars(Next)

StateConstraint == Len(history) <= MaxLen
CONSTRAINT StateConstraint

EventuallyDone == <> (pc = "Done")

=============================================================================