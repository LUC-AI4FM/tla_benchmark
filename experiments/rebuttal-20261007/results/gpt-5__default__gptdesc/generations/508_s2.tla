----------------------------- MODULE SmallPlusCalTrans -----------------------------

EXTENDS Naturals

CONSTANTS XRange
ASSUME XRange = 1..10

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x \in XRange
  /\ pc = "Start"

DoStep ==
  /\ pc = "Start"
  /\ x^2 <= 100
  /\ pc' = "Done"
  /\ UNCHANGED x

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == DoStep \/ Stutter

Spec == Init /\ [] Next

Termination == <> (pc = "Done")

=============================================================================