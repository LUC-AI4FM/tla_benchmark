---- MODULE SimpleAssertion ----
EXTENDS Integers, TLC

VARIABLES x, pc

vars == <<x, pc>>

Init ==
  /\ x \in 1..10
  /\ pc = "Lbl_1"

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ Assert(x^2 <= 100, "Assertion x^2 <= 100 failed")
  /\ pc' = "Done"
  /\ x' = x

Next == Lbl_1

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================