------------------------------- MODULE Counter -------------------------------
(***************************************************************************)
(* A single integer-valued counter that starts at 1 and increases by       *)
(* exactly one per step until it reaches 5, after which it remains fixed   *)
(* forever.                                                                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Max

ASSUME MaxAssumption == Max = 5

VARIABLE x

vars == << x >>

-----------------------------------------------------------------------------
(* Initialization *)

Init == x = 1

(* The counter increments by exactly 1 while below Max. *)
Increment ==
    /\ x < Max
    /\ x' = x + 1

(* Once at Max, the counter remains unchanged. *)
Stay ==
    /\ x = Max
    /\ UNCHANGED x

Next == Increment \/ Stay

(* Weak fairness: if Increment stays continuously enabled, it must        *)
(* eventually occur.                                                       *)
Fairness == WF_vars(Increment)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties and auxiliary invariants *)

(* Bounds: the counter always stays in 1..Max. *)
TypeOK == x \in 1..Max

BoundsInv == 1 <= x /\ x <= Max

(* Every step either increments by one (when below Max) or leaves the     *)
(* counter unchanged (when at Max).                                        *)
StepSafety ==
    [][ \/ (x < Max /\ x' = x + 1)
        \/ (x = Max /\ x' = x) ]_vars

(* Monotonicity: the counter never decreases. *)
Monotonic == [][x' >= x]_vars

(* The counter never jumps by more than one. *)
NoJump == [][x' = x \/ x' = x + 1]_vars

(* Once at Max, it stays at Max. *)
StaysAtMax == [](x = Max => [](x = Max))

-----------------------------------------------------------------------------
(* Liveness properties *)

(* The counter eventually reaches Max. *)
EventuallyMax == <>(x = Max)

(* Eventual stabilization: eventually the counter is Max forever. *)
Stabilization == <>[](x = Max)

(* Progress: whenever below Max, the counter eventually increases. *)
Progress == \A k \in 1..(Max - 1) : (x = k) ~> (x = k + 1)

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM Spec => []TypeOK
THEOREM Spec => []BoundsInv
THEOREM Spec => StepSafety
THEOREM Spec => Monotonic
THEOREM Spec => NoJump
THEOREM Spec => StaysAtMax
THEOREM Spec => EventuallyMax
THEOREM Spec => Stabilization
THEOREM Spec => Progress

=============================================================================