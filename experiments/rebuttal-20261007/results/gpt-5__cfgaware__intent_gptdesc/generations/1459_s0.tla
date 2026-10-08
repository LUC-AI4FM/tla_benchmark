------------------------------ MODULE SaturatingCounter ------------------------------

EXTENDS Naturals

(*
  A non-decreasing counter with saturation at Limit = 3.
  Required names exported for model checking: Limit, Spec.
*)

Limit == 3

VARIABLE x

Init ==
  x = 0

Inc ==
  /\ x < Limit
  /\ x' = x + 1

(*
  Transition relation: increments by 1 when below the limit.
  Stuttering (x' = x) is permitted at any time via [Next]_x in Spec.
*)
Next ==
  Inc

(*
  Temporal specification:
  - Start from Init
  - Steps always satisfy Next or stutter on x
  - Weak fairness on Inc ensures progress when enabled, so the counter
    eventually reaches the saturation value.
*)
Spec ==
  /\ Init
  /\ [][Next]_x
  /\ WF_x(Inc)

(*
  State invariants (safety):
  - x is always a natural number
  - x never exceeds the Limit
*)
TypeInv ==
  x \in Nat

BoundInv ==
  x <= Limit

(*
  Action properties (safety over steps):
  - Never decreases
  - No illegal jumps: each step changes x by at most 1 (or stutters)
  - Once saturated (x >= Limit), the state remains unchanged
*)
NonDecr ==
  x' >= x

NoJump ==
  x' \in {x, x + 1}

SaturatedStable ==
  (x >= Limit) => (x' = x)

(*
  Model-checkable safety/liveness properties:
*)
AlwaysType ==
  [] TypeInv

AlwaysBound ==
  [] BoundInv

AlwaysNonDecr ==
  [] NonDecr

AlwaysNoJump ==
  [] NoJump

AlwaysSaturatedStable ==
  [] SaturatedStable

(*
  Liveness: from the initial state, the counter eventually reaches saturation.
*)
Live ==
  <> (x = Limit)

=============================================================================