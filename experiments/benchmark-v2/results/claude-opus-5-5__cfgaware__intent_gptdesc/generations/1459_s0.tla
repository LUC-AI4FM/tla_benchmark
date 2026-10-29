---------------------------- MODULE SaturatingCounter ----------------------------
EXTENDS Naturals

CONSTANT Limit

ASSUME LimitIsNat == Limit \in Nat

VARIABLE count

vars == << count >>

-----------------------------------------------------------------------------
(* Initial condition: the counter starts at zero.                           *)
Init == count = 0

(* Increment step: only enabled while strictly below the threshold.         *)
Increment ==
    /\ count < Limit
    /\ count' = count + 1

(* Once saturated, the counter stays unchanged forever.                     *)
Saturated ==
    /\ count >= Limit
    /\ UNCHANGED count

(* Allowed transition relation (stuttering added by [Next]_vars).           *)
Next == Increment \/ Saturated

(* Temporal behavior: weak fairness on Increment ensures progress.          *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Increment)

-----------------------------------------------------------------------------
(* Safety properties                                                         *)

TypeOK == count \in Nat

BoundedByLimit == count <= Limit

Invariant == TypeOK /\ BoundedByLimit

(* The counter never decreases.                                              *)
NeverDecreases == [][count' >= count]_vars

(* No illegal jumps: each step either stutters or adds exactly one,          *)
(* and an increment never goes past the threshold.                           *)
NoIllegalJumps == [][count' = count \/ (count' = count + 1 /\ count' <= Limit)]_vars

(* Once at the limit, it stays at the limit.                                 *)
StaysSaturated == [][count >= Limit => count' = count]_vars

-----------------------------------------------------------------------------
(* Liveness properties                                                       *)

EventuallySaturated == <>(count = Limit)

EventuallyAlwaysSaturated == <>[](count = Limit)

Progress == \A n \in 0..Limit : (count = n) ~> (count = Limit)

-----------------------------------------------------------------------------
(* Proof obligations (checkable by TLC with the configuration).              *)

THEOREM SafetyThm == Spec => []Invariant
THEOREM MonotoneThm == Spec => NeverDecreases
THEOREM NoJumpThm == Spec => NoIllegalJumps
THEOREM LivenessThm == Spec => EventuallySaturated
=============================================================================