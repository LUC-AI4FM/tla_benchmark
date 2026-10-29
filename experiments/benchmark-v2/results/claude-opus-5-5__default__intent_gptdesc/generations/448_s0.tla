---------------------------- MODULE Counter ----------------------------
(***************************************************************************)
(* A state machine with one integer variable x that can be incremented by *)
(* one, repeatedly and forever. Stuttering steps (x' = x) are allowed.     *)
(*                                                                         *)
(* Two variants are provided:                                              *)
(*   - Spec        : the unbounded system. Init is x \in Nat, which TLC    *)
(*                   cannot enumerate. To model check it, override Nat     *)
(*                   with 0..K in the model, add the CONSTRAINT            *)
(*                   StateConstraint, and check the safety properties.     *)
(*   - BoundedSpec : x starts in 0..MaxValue and never exceeds MaxValue.   *)
(*                   This variant is finite and checkable directly         *)
(*                   (invariants TypeOK and BoundInv). The liveness        *)
(*                   properties hold only for Spec. In BoundedSpec,        *)
(*                   increments are intentionally disabled at MaxValue.    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxValue          \* upper bound used by the bounded variant
ASSUME MaxValue \in Nat

VARIABLE x

vars == <<x>>

-----------------------------------------------------------------------------
(* Unbounded system                                                        *)

Init == x \in Nat

Inc == x' = x + 1

Next == Inc

Spec == Init /\ [][Next]_vars /\ WF_vars(Inc)

-----------------------------------------------------------------------------
(* Bounded system                                                          *)

BoundedInit == x \in 0..MaxValue

BoundedInc == x < MaxValue /\ Inc

BoundedNext == BoundedInc

BoundedSpec == BoundedInit /\ [][BoundedNext]_vars /\ WF_vars(BoundedInc)

\* State constraint for model checking Spec over a finite fragment.
StateConstraint == x <= MaxValue

-----------------------------------------------------------------------------
(* Safety properties                                                       *)

\* The value is always a natural number.
TypeOK == x \in Nat

\* The value stays within the bound. This is an invariant of BoundedSpec.
BoundInv == x <= MaxValue

\* Every step that changes x strictly increases it.
Monotonicity == [][x' > x]_vars

\* Every Inc step increases x by exactly one.
IncByOne == [][Inc => x' = x + 1]_vars

\* No unintended jumps: every step changes x by 0 or by +1.
NoUnintendedJumps == [][x' = x \/ x' = x + 1]_vars

-----------------------------------------------------------------------------
(* Liveness properties (these hold for Spec)                               *)

\* Increments are never permanently disabled.
IncAlwaysEnabled == [](ENABLED <<Inc>>_vars)

\* From any reachable state, another increment eventually happens.
EventuallyIncrement == []<><<Inc>>_vars

\* From any reachable state, x eventually grows past its current value.
AlwaysGrows == \A n \in Nat : (x = n) ~> (x > n)

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => Monotonicity /\ IncByOne /\ NoUnintendedJumps
THEOREM Spec => IncAlwaysEnabled /\ EventuallyIncrement /\ AlwaysGrows
THEOREM BoundedSpec => [](TypeOK /\ BoundInv)
THEOREM BoundedSpec => Monotonicity /\ IncByOne /\ NoUnintendedJumps
=============================================================================