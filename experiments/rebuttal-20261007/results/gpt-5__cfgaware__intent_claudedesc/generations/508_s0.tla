------------------------------ MODULE SquareAssertPlusCal ------------------------------

EXTENDS Naturals, TLC

(*
--algorithm AssertCheck
variables x \in 1..10;
begin
  A:
    assert x * x <= 100;
  Done:
    skip;
end algorithm;
*)

(*
  The following TLA+ definitions are the (handwritten) PlusCal translation.
*)
VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x \in 1..10
  /\ pc = "A"

Next ==
  \/ /\ pc = "A"
     /\ Assert(x * x <= 100, "Assertion failed: x^2 exceeds 100")
     /\ pc' = "Done"
     /\ UNCHANGED x

Spec ==
  Init /\ [][Next]_vars

Termination ==
  <> (pc = "Done")

==============================