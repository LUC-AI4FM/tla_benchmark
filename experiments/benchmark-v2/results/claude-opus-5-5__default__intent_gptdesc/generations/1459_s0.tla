------------------------------- MODULE SaturatingCounter -------------------------------
EXTENDS Naturals

CONSTANT Max

ASSUME MaxAssumption == Max \in Nat /\ Max = 3

VARIABLE x

vars == << x >>

---------------------------------------------------------------------------------------
(* Initial condition                                                                 *)
---------------------------------------------------------------------------------------
Init == x = 0

---------------------------------------------------------------------------------------
(* Transition relation                                                               *)
---------------------------------------------------------------------------------------
Increment ==
    /\ x < Max
    /\ x' = x + 1

Next == Increment

---------------------------------------------------------------------------------------
(* Temporal behavior                                                                 *)
---------------------------------------------------------------------------------------
\* Safety part only: stuttering steps are permitted at any time.
SafetySpec == Init /\ [][Next]_vars

\* Weak fairness on Increment is needed for the liveness claim.
Spec == SafetySpec /\ WF_vars(Increment)

---------------------------------------------------------------------------------------
(* Safety properties (state invariants)                                              *)
---------------------------------------------------------------------------------------
TypeOK == x \in Nat

NeverExceeds == x <= Max

InRange == x \in 0..Max

\* Inductive invariant that implies all of the state invariants above.
IndInv == x \in 0..Max

---------------------------------------------------------------------------------------
(* Safety properties (action / temporal)                                             *)
---------------------------------------------------------------------------------------
\* The counter never decreases.
NonDecreasing == [][x' >= x]_vars

\* No illegal jumps: every step either stutters or increments by exactly one.
NoIllegalJumps == [][x' = x \/ x' = x + 1]_vars

\* No increment takes the state above the threshold.
NoOvershoot == [][x' <= Max]_vars

\* Once saturated, the counter remains unchanged forever.
SaturationStable == [][x >= Max => x' = x]_vars

SafetyProperties ==
    /\ []TypeOK
    /\ []NeverExceeds
    /\ NonDecreasing
    /\ NoIllegalJumps
    /\ NoOvershoot
    /\ SaturationStable

---------------------------------------------------------------------------------------
(* Liveness properties                                                               *)
---------------------------------------------------------------------------------------
\* The counter eventually reaches the saturation value.
EventuallySaturates == <>(x = Max)

\* The counter eventually reaches the saturation value and stays there forever.
EventuallyAlwaysSaturated == <>[](x = Max)

\* Progress: whenever below the threshold, the counter eventually increases.
Progress == \A n \in 0..(Max - 1) : (x = n) ~> (x = n + 1)

\* Variant (ranking function) used to justify termination of increments.
Variant == Max - x

VariantDecreases == [][x < Max => (Variant' < Variant \/ x' = x)]_vars

---------------------------------------------------------------------------------------
(* Proof obligations / model-checkable theorems                                     *)
---------------------------------------------------------------------------------------
THEOREM InitEstablishesInv == Init => IndInv

THEOREM InvIsInductive == IndInv /\ [Next]_vars => IndInv'

THEOREM InvImpliesSafety == IndInv => (TypeOK /\ NeverExceeds /\ InRange)

THEOREM SafetyTheorem == SafetySpec => SafetyProperties

THEOREM VariantTheorem == SafetySpec => VariantDecreases

THEOREM LivenessTheorem == Spec => EventuallySaturates

THEOREM StableLivenessTheorem == Spec => EventuallyAlwaysSaturated

THEOREM ProgressTheorem == Spec => Progress

=======================================================================================