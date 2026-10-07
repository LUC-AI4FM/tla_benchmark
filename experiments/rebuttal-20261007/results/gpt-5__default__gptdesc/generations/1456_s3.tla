----------------------------- MODULE TinySetMachine -----------------------------

EXTENDS Naturals, TLC

CONSTANTS
    ExpectedFullSet,
    ExpectedGainThree

ASSUME ExpectedFullSet \in Nat
ASSUME ExpectedGainThree \in Nat

VARIABLES x, y

vars == << x, y >>

Universe == {1, 2, 3}

(*
  State predicates and actions of interest
*)
FullSet == x = Universe

GainThree == /\ ~(3 \in x)
             /\  3 \in x'

(*
  Initial condition: x and y are subsets of Universe and x is contained in y
*)
Init ==
  /\ x \subseteq Universe
  /\ y \subseteq Universe
  /\ x \subseteq y

(*
  Next-state relation: y is unchanged; x' is any subset of y' (which equals y)
*)
Next ==
  /\ y' = y
  /\ x' \in SUBSET y'

(*
  Basic safety invariants (state predicates)
*)
TypeOK == /\ x \subseteq Universe
          /\ y \subseteq Universe

XSubsetY == x \subseteq y

Inv == TypeOK /\ XSubsetY

(*
  Temporal specification (no fairness conditions)
*)
Spec == Init /\ [][Next]_vars

(*
  Optional derived temporal safety property expressing that y never changes
*)
YUnchanged == []UNCHANGED y

(*
  TLC metadata inspection and assertions about named predicate counts.
  These refer to TLC's exploration metadata keyed by the given names.
  They are asserted to match the expected counts provided as constants.
*)
CoverageFullSet   == TLCGet("numOf:FullSet")
CoverageGainThree == TLCGet("numOf:GainThree")

CoverageAssertions ==
  /\ Assert(CoverageFullSet   = ExpectedFullSet,   "Unexpected count for FullSet")
  /\ Assert(CoverageGainThree = ExpectedGainThree, "Unexpected count for GainThree")

===============================================================================