------------------------------- MODULE TwoStateConstraint -------------------------------

EXTENDS Sequences

VARIABLES pc, history

vars == << pc, history >>

Init ==
  /\ pc = "A"
  /\ history = << >>

A ==
  /\ pc = "A"
  /\ pc' = "B"
  /\ history' = history \o << pc >>

B ==
  /\ pc = "B"
  /\ pc' = "A"
  /\ history' = history

Next == A \/ B

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Constraint == Len(history) < 3

Prop == <> (pc = "Done")

=============================================================================