----------------------------- MODULE SmallPlusCal -----------------------------
EXTENDS Integers

VARIABLES x, pc

Init ==
  /\ x \in 1..10
  /\ pc = "l1"

L1 ==
  /\ pc = "l1"
  /\ x^2 <= 100
  /\ pc' = "Done"
  /\ UNCHANGED x

Done ==
  /\ pc = "Done"
  /\ pc' = "Done"
  /\ UNCHANGED x

Next == L1 \/ Done

vars == << x, pc >>

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")
=============================================================================