------------------------------ MODULE TwoIntsStutter ------------------------------

EXTENDS Integers

(*
  A simple concurrent system with two integer-valued state locations that
  are initialized to zero and never change thereafter.
*)

VARIABLES x, y

Vars == << x, y >>

(*
  Initial condition: both locations are zero and equal.
  This also makes the initial state unique (deterministic).
*)
Init ==
  /\ x = 0
  /\ y = 0
  /\ x = y

(*
  Transition relation: only stuttering (no-change) steps are allowed.
*)
Next ==
  UNCHANGED Vars

(*
  Full behavior specification: start in Init, then only stuttering steps forever.
*)
Spec ==
  /\ Init
  /\ [][Next]_Vars

(*
  Basic typing: both locations are integers.
*)
TypeOK ==
  /\ x \in Int
  /\ y \in Int

(*
  Invariants and properties to be checked.
*)

(*
  Initial-state invariant: both locations are zero and equal.
  Under Spec, this holds initially and forever.
*)
InvInitZeroEq ==
  /\ x = 0
  /\ y = 0
  /\ x = y

(*
  Equality invariant: the two locations are always equal.
*)
EqInvariant ==
  x = y

(*
  Alias commonly used by model configs.
*)
Inv == EqInvariant

(*
  Safety: there is no reachable state that violates equality.
*)
SafetyNoDivergence ==
  [] (x = y)

(*
  Temporal property: all subsequent steps preserve values unchanged.
*)
AlwaysNoChange ==
  [] UNCHANGED Vars

(*
  Action-level preservation: whenever a step leaves both variables unchanged,
  equality is preserved by that step (vacuously true here, and holds for all steps).
*)
EqualityPreservedOnNoChange ==
  [] (UNCHANGED Vars => x' = y')

(*
  Temporal assertion that the initial condition holds at time 0.
  TLC can check this as a PROPERTY.
*)
TemporalInitHolds ==
  Init

=============================================================================