------------------------------ MODULE SmallPlusCal ------------------------------

EXTENDS Naturals, Integers

CONSTANTS Dummy

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x \in 1..10
  /\ pc = "L1"

L1Step ==
  /\ pc = "L1"
  /\ x ^ 2 <= 100
  /\ x' = x
  /\ pc' = "Done"

DoneStep ==
  /\ pc = "Done"
  /\ x' = x
  /\ pc' = "Done"

Next ==
  L1Step \/ DoneStep

Spec ==
  Init /\ [][Next]_vars

\* Safety invariant corresponding to the checked assertion
AssertInv == x ^ 2 <= 100

\* Liveness: eventual termination
Termination == <> (pc = "Done")

===============================================================================