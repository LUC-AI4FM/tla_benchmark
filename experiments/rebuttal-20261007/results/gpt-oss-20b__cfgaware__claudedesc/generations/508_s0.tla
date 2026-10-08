------------------------------ MODULE ArithmeticAssertion ------------------------------
EXTENDS Naturals

(*--------------------------------------------------------------------
  This module models a single-step sequential algorithm that
  nondeterministically initializes an integer variable `x` in the range
  1..10 and then asserts that `x^2 ≤ 100`.  The program counter `pc`
  moves from "Lbl_1" to "Done".  A stuttering action keeps `pc`
  at "Done" forever.  The temporal specification `Spec` is the
  conjunction of the initial condition and the always-enabled next-state
  relation.  An auxiliary liveness property `Termination` states that
  eventually `pc = "Done"`.  The assertion holds for all possible
  initializations, so TLC will verify it.
--------------------------------------------------------------------*)

VARIABLES x, pc

(*--@type x : 1..10 *)
(*--@type pc : {"Lbl_1", "Done"} *)

Init == /\ x \in 1..10
        /\ pc = "Lbl_1"

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ x * x <= 100
  /\ pc' = "Done"
  /\ UNCHANGED x

Terminating ==
  /\ pc = "Done"
  /\ pc' = pc

Next == Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_<<x, pc>>

Termination == <> (pc = "Done")

=============================================================================