------------------------------ MODULE Counter ------------------------------

EXTENDS Naturals, Integers

CONSTANT UB
VARIABLE c

vars == << c >>

Init ==
  /\ UB \in Nat
  /\ c = 0

Inc ==
  /\ c < UB
  /\ c' = c + 1

Stay ==
  /\ c = UB
  /\ c' = c

Next == Inc \/ Stay

Spec == Init /\ [][Next]_c /\ WF_c(Inc)

(*
  Safety invariant: the counter always remains within bounds.
*)
TypeInv == c \in 0..UB

(*
  Liveness: the counter eventually reaches the bound.
*)
Termination == <> (c = UB)

(*
  Stability at bound: once the counter reaches the bound, it remains there forever.
*)
StableAtBound == [] (c = UB => [] (c = UB))

=============================================================================