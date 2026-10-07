------------------------------ MODULE AlternatingAB ------------------------------

EXTENDS Naturals, Sequences

CONSTANT MaxLen
ASSUME MaxLen \in Nat

VARIABLES pc, history

vars == << pc, history >>

PCStates == {"A", "B", "Done"}

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

TypeOK ==
  /\ pc \in PCStates
  /\ history \in Seq({"A"})

StateConstraint == Len(history) <= MaxLen

EventuallyDone == <> (pc = "Done")

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

===============================================================================