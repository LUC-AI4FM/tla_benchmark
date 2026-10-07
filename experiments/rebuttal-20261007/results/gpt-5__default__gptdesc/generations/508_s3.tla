--------------------------- MODULE SmallPlusCal ---------------------------

EXTENDS Naturals

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x \in 1..10
  /\ pc = "L"

Lbl ==
  /\ pc = "L"
  /\ x^2 <= 100
  /\ x' = x
  /\ pc' = "Done"

DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  Lbl \/ DoneStutter

TypeOK ==
  /\ x \in 1..10
  /\ pc \in {"L", "Done"}

AssertOK ==
  x^2 <= 100

Termination ==
  <> (pc = "Done")

Spec ==
  Init /\ [][Next]_vars /\ Termination

============================================================================