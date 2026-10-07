------------------------------- MODULE SmallPlusCal -------------------------------
EXTENDS Integers, TLC

CONSTANTS N
ASSUME N = 10

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x \in 1..N
  /\ pc = "L1"

Step ==
  /\ pc = "L1"
  /\ Assert(x^2 <= 100, "Assertion x^2 <= 100 failed")
  /\ pc' = "Done"
  /\ x' = x

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Step \/ Stutter

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ x \in 1..N
  /\ pc \in {"L1", "Done"}

AssertOK ==
  x^2 <= 100

Termination == <> (pc = "Done")
=============================================================================