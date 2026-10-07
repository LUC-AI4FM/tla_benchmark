------------------------------ MODULE SmallPlusCal ------------------------------

EXTENDS Integers

CONSTANTS Range

ASSUME Range = 1..10

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x \in Range
  /\ pc = "Start"

Check ==
  /\ pc = "Start"
  /\ x^2 <= 100
  /\ x' = x
  /\ pc' = "Done"

DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Check \/ DoneStutter

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ x \in Range
  /\ pc \in {"Start", "Done"}

AssertInv == x^2 <= 100

Termination == <> (pc = "Done")

===============================================================================