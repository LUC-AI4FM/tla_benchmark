------------------------------ MODULE ArithmeticAssertion ------------------------------

EXTENDS Integers, TLC

CONSTANTS L, U
ASSUME L = 1 /\ U = 10

VARIABLES x, pc

Vars == << x, pc >>

Init ==
  /\ x \in L..U
  /\ pc = "Lbl_1"

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ Assert(x * x <= 100, "Assertion x^2 <= 100 failed")
  /\ x' = x
  /\ pc' = "Done"

Terminating ==
  /\ pc = "Done"
  /\ x' = x
  /\ pc' = "Done"

Next == Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_Vars

TypeOK ==
  /\ x \in L..U
  /\ pc \in {"Lbl_1", "Done"}

SquareLeq100 == x * x <= 100

Inv == TypeOK /\ SquareLeq100

Termination == <> (pc = "Done")

=============================================================================