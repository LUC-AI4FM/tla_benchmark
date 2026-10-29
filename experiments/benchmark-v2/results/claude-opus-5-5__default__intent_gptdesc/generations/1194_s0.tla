---------------------------- MODULE StableTriple ----------------------------
(***************************************************************************)
(* A simple concurrent-state system with three independent integer         *)
(* components. Initially each component may take any value in its own      *)
(* finite range:                                                           *)
(*   x \in 1..100,  y \in 1..200,  z \in 1..20                             *)
(* so the initial state space is the full Cartesian product of the three   *)
(* ranges (100 * 200 * 20 = 400,000 states). After initialization the      *)
(* system never changes state: the transition relation is the identity.    *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES x, y, z

vars == << x, y, z >>

\* The three component ranges
XRange == 1..100
YRange == 1..200
ZRange == 1..20

-----------------------------------------------------------------------------
(* Type correctness: each component stays within its range.               *)
TypeOK ==
    /\ x \in XRange
    /\ y \in YRange
    /\ z \in ZRange

(* Initial-state predicate: exactly the specified ranges and nothing else. *)
(* The components are not related to each other in any way.               *)
Init ==
    /\ x \in XRange
    /\ y \in YRange
    /\ z \in ZRange

(* Transition relation: identity, so every step preserves all values.     *)
Next ==
    /\ x' = x
    /\ y' = y
    /\ z' = z

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties                                                       *)

\* Trivial baseline invariant (a tautology).
TrivialInv == TRUE

\* Combined invariant that should hold in every reachable state.
Inv == TrivialInv /\ TypeOK

\* No transition changes any component value.
NoChange == [][UNCHANGED vars]_vars

-----------------------------------------------------------------------------
(* Liveness: the system can remain forever without state changes; from    *)
(* some point on (in fact, from the start) every step is a stuttering      *)
(* step.                                                                   *)
RemainsStable == <>[][UNCHANGED vars]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => NoChange
THEOREM Spec => RemainsStable
=============================================================================