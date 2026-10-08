------------------------------ MODULE ArithmeticAssert ------------------------------

EXTENDS Integers, Naturals, TLC

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ pc = "Lbl_1"
  /\ x \in 1..10

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ Assert(x^2 <= 100, "Assertion failed: x^2 <= 100")
  /\ x' = x
  /\ pc' = "Done"

Terminating ==
  /\ pc = "Done"
  /\ x' = x
  /\ pc' = "Done"

Next == Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

=============================================================================