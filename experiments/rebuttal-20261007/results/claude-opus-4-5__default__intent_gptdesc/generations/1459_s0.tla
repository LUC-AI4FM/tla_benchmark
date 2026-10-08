---------------------------- MODULE SaturatingCounter ----------------------------
(***************************************************************************)
(* A TLA+ specification of a non-decreasing counter with saturation point. *)
(* The counter starts at 0, can increment by 1, and saturates at 3.        *)
(***************************************************************************)

EXTENDS Integers, Naturals

CONSTANTS Threshold

ASSUME ThresholdAssumption == Threshold = 3

VARIABLES counter

(***************************************************************************)
(* Type invariant: counter is always a natural number                      *)
(***************************************************************************)
TypeInvariant == counter \in Nat

(***************************************************************************)
(* Initial condition: counter starts at zero                               *)
(***************************************************************************)
Init == counter = 0

(***************************************************************************)
(* Increment action: increase counter by 1 if below threshold              *)
(***************************************************************************)
Increment == 
    /\ counter < Threshold
    /\ counter' = counter + 1

(***************************************************************************)
(* Stutter action: counter remains unchanged (always enabled)              *)
(***************************************************************************)
Stutter == 
    /\ counter' = counter

(***************************************************************************)
(* Next state relation: either increment (if possible) or stutter          *)
(***************************************************************************)
Next == Increment \/ Stutter

(***************************************************************************)
(* Specification with weak fairness on Increment to ensure progress        *)
(***************************************************************************)
Spec == Init /\ [][Next]_counter /\ WF_counter(Increment)

-----------------------------------------------------------------------------
(***************************************************************************)
(*                          SAFETY PROPERTIES                              *)
(***************************************************************************)

(***************************************************************************)
(* Safety: counter is always a natural number                              *)
(***************************************************************************)
SafetyNatural == counter \in Nat

(***************************************************************************)
(* Safety: counter never exceeds the threshold (saturation value)          *)
(***************************************************************************)
SafetyBounded == counter <= Threshold

(***************************************************************************)
(* Safety: counter never decreases (non-decreasing property)               *)
(* Expressed as: if we take a step, counter doesn't decrease               *)
(***************************************************************************)
SafetyNonDecreasing == [][counter' >= counter]_counter

(***************************************************************************)
(* Safety: no illegal jumps - counter changes by at most 1                 *)
(***************************************************************************)
SafetyNoJumps == [][counter' \in {counter, counter + 1}]_counter

(***************************************************************************)
(* Combined safety invariant (state predicate)                             *)
(***************************************************************************)
SafetyInvariant == 
    /\ counter \in Nat
    /\ counter >= 0
    /\ counter <= Threshold

(***************************************************************************)
(* Inductive invariant for proving safety                                  *)
(***************************************************************************)
InductiveInvariant == counter \in 0..Threshold

-----------------------------------------------------------------------------
(***************************************************************************)
(*                         LIVENESS PROPERTIES                             *)
(***************************************************************************)

(***************************************************************************)
(* Liveness: counter eventually reaches the saturation value               *)
(***************************************************************************)
LivenessReachesSaturation == <>(counter = Threshold)

(***************************************************************************)
(* Liveness: counter eventually reaches 3 (explicit threshold value)       *)
(***************************************************************************)
LivenessReachesThree == <>(counter = 3)

(***************************************************************************)
(* Once saturated, counter stays at threshold forever                      *)
(***************************************************************************)
SaturationStable == [](counter = Threshold => [](counter = Threshold))

(***************************************************************************)
(* Alternative: leads-to property - being below threshold leads to         *)
(* eventually reaching threshold                                           *)
(***************************************************************************)
ProgressToSaturation == (counter < Threshold) ~> (counter = Threshold)

-----------------------------------------------------------------------------
(***************************************************************************)
(*                    PROOF OBLIGATIONS / THEOREMS                         *)
(***************************************************************************)

(***************************************************************************)
(* Theorem: Safety invariant holds initially                               *)
(***************************************************************************)
THEOREM InitEstablishesInvariant == Init => SafetyInvariant

(***************************************************************************)
(* Theorem: Safety invariant is preserved by Next                          *)
(***************************************************************************)
THEOREM InvariantPreserved == SafetyInvariant /\ Next => SafetyInvariant'

(***************************************************************************)
(* Theorem: Inductive invariant is indeed inductive                        *)
(***************************************************************************)
THEOREM InductiveInvariantIsInductive ==
    /\ Init => InductiveInvariant
    /\ InductiveInvariant /\ Next => InductiveInvariant'

(***************************************************************************)
(* Main correctness theorem: Spec satisfies all properties                 *)
(***************************************************************************)
THEOREM Correctness ==
    Spec => /\ []SafetyInvariant
            /\ SafetyNonDecreasing
            /\ SafetyNoJumps
            /\ LivenessReachesSaturation
            /\ SaturationStable

=============================================================================