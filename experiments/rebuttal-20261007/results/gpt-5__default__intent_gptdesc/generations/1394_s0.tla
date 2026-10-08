----------------------------- MODULE ThreeComponentSystem -----------------------------

EXTENDS Integers, TLC

(*
  Three components:
  - x: regularly updated (incremented)
  - y: may be left unchanged by some transitions (and never changes while increment is enabled)
  - C: externally supplied constant (not a variable; provided by instantiation)
*)

CONSTANTS
  N,        \* termination bound for x
  YSet,     \* finite domain of y
  CSet,     \* finite domain for external constant C
  C,        \* externally supplied constant in CSet
  XInit,    \* allowed initial values for x (subset of 0..N)
  YInit     \* allowed initial values for y (subset of YSet)

ASSUME N \in Nat
ASSUME IsFiniteSet(YSet) /\ YSet # {}
ASSUME IsFiniteSet(CSet) /\ CSet # {}
ASSUME C \in CSet
ASSUME XInit \subseteq 0..N /\ XInit # {}
ASSUME YInit \subseteq YSet /\ YInit # {}

VARIABLES x, y

V == << x, y >>

TypeInv ==
  /\ x \in 0..N
  /\ y \in YSet
  /\ C \in CSet

Init ==
  /\ x \in XInit
  /\ y \in YInit

Guard == x < N

Inc ==
  /\ Guard
  /\ x' = x + 1
  /\ y' = y

Term ==
  /\ x = N
  /\ x' = x
  /\ UNCHANGED y

Next == Inc \/ Term

Spec == Init /\ [][Next]_V /\ WF_V(Inc)

(*
  Safety and invariants
*)
AlwaysTypeInv == []TypeInv

\* The unchanged component never changes in any step whose source state enables increment.
SafetyYWhileEnabled == []( Guard => (y' = y) )

\* The externally supplied constant remains equal to its initially supplied value (trivial for a CONSTANT).
C0 == C
SafetyConstFixed == [](C = C0)

(*
  Progress and liveness
*)
\* Increment is enabled repeatedly while below the bound.
ProgressEnabled == []( Guard => ENABLED Inc )

\* From any state where the incrementing guard holds, eventually an increment step occurs.
LivenessInc == []( Guard => <>Inc )

================================================================================