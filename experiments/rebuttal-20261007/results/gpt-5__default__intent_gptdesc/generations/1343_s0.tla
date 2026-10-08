----------------------------- MODULE TwoStableInts -----------------------------

EXTENDS Integers

CONSTANTS Values
ASSUME Values = Int

VARIABLES x, y

vars == << x, y >>

(*
  State space typing for both integer-valued locations
*)
TypeOK == /\ x \in Values
          /\ y \in Values

(*
  Initial condition: both locations are zero (and hence equal)
*)
Init == /\ x = 0
        /\ y = 0

(*
  Only allowed transition is a stuttering/no-change step
*)
NoChange == UNCHANGED vars

Next == NoChange

(*
  Complete behavior specification
*)
Spec == Init /\ [][Next]_vars

(*
  Safety invariants and properties
*)

(*
  Initial-state invariant: both are zero and equal
*)
InitInv == /\ x = 0
           /\ y = 0
           /\ x = y

(*
  Equality invariant (holds in all reachable states for this Spec)
*)
EqualityInv == x = y

(*
  Action-level preservation: if a step does not change either value,
  then equality is preserved by that step.
*)
PreservesEquality == (x = y) /\ NoChange => x' = y'

(*
  Temporal properties:
  - All subsequent steps are no-change steps (no modifications occur).
  - Equality holds at all times (safety w.r.t. unintended divergence).
  - The initial condition holds at time 0.
*)
AllStepsUnchanged == [] [NoChange]_vars
Safety_NoUnintendedDivergence == [] EqualityInv
InitialConditionAtTime0 == Init

=============================================================================