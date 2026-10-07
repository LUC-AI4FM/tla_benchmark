------------------------------ MODULE TwoStateProcess ------------------------------

EXTENDS Naturals, Sequences

CONSTANT MaxLen
ASSUME MaxLen \in Nat

VARIABLES pc, hist

vars == << pc, hist >>

Init ==
  /\ pc = "A"
  /\ hist = << >>

A ==
  /\ pc = "A"
  /\ pc' = "B"
  /\ hist' = Append(hist, pc)

B ==
  /\ pc = "B"
  /\ pc' = "A"
  /\ hist' = hist

Next == A \/ B

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

StateConstraint == Len(hist) <= MaxLen

EventuallyDone == <> (pc = "Done")

=============================================================================