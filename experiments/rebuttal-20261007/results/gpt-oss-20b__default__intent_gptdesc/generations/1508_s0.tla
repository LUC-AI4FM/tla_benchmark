------------------------------ MODULE FiniteIntSM ------------------------------
EXTENDS Naturals

CONSTANTS DOMAIN, INITIAL

VARIABLE x

(* Type invariant *)
TypeInvariant == x \in DOMAIN

(* Initial condition *)
Init == x = INITIAL

(* Transition relation *)
Next ==
  \/ (x' = 0)
  \/ (x' \in {x + 1, x + 2})
  \/ (x = 3 /\ x' = 10)
  \/ (x = 2 /\ x' \in {4,5})
  \/ (x' = 100)

(* Specification *)
Spec == Init /\ [][Next]_<<x>>

(* Safety property *)
Safety == TypeInvariant /\ (x = INITIAL)

=============================================================================