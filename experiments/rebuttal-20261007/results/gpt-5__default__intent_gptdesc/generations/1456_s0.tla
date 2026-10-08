---- MODULE MutableSubset ----
EXTENDS TLC

CONSTANTS UNIVERSE, InitCap

ASSUME UNIVERSE = {1, 2, 3}
ASSUME InitCap \subseteq UNIVERSE /\ InitCap # UNIVERSE

VARIABLES U, S

vars == << U, S >>

Init ==
  /\ U = UNIVERSE
  /\ S \in SUBSET InitCap

Next ==
  /\ U' = U
  /\ S' \in SUBSET U

Spec ==
  Init /\ [][Next]_vars

(*
  State predicates (safety and reachability markers)
*)
TypeOK ==
  /\ U = UNIVERSE
  /\ S \subseteq U

SafetyInv ==
  S \subseteq U

UniverseInvariant ==
  U = UNIVERSE

FullReached ==
  S = U

(*
  Action-level predicates to reason about element gains and specific transitions.
  These can be used as Action Properties in TLC or within temporal formulas.
*)
ElementGained(e) ==
  /\ e \in U
  /\ e \notin S
  /\ e \in S'

GainElem(e) ==
  /\ Next
  /\ ElementGained(e)

Gain3Action ==
  GainElem(3)

(*
  Convenience: an action that reaches the full universe in one step.
*)
FullStep ==
  /\ Next
  /\ S' = U

(*
  Enabledness (state) predicates for one-step reachability.
*)
CanGain(e) ==
  Enabled GainElem(e)

CanReachFullInOne ==
  Enabled FullStep

(*
  Temporal “possibility” properties (existential-style reachability markers).
  Note: These are named liveness formulas you can model-check as properties.
*)
Angle(A) == A /\ vars' # vars

MayReachFull ==
  <> FullReached

MayGain(e) ==
  <> Angle(GainElem(e))

MayGain3 ==
  <> Angle(GainElem(3))
====