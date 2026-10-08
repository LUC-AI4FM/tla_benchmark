------------------------------ MODULE Counter ------------------------------
EXTENDS Naturals, TLC

CONSTANTS Limit          \* Saturation point (e.g., 3)

VARIABLE state

(* ------------------------------------------------------------------ *)
(* Initial condition: the counter starts at zero.                     *)
Init == state = 0

(* ------------------------------------------------------------------ *)
(* Increment step: allowed only when the current value is strictly   *)
(* less than the saturation limit.                                   *)
Increment == state' = state + 1 /\ state < Limit

(* Stuttering step: the state may stay unchanged.                    *)
Stutter == state' = state

(* Next relation: either increment or stutter.                        *)
Next == Increment \/ Stutter

(* ------------------------------------------------------------------ *)
(* Temporal specification of the system.                              *)
Spec == Init /\ [][Next]_state

(* ------------------------------------------------------------------ *)
(* Safety properties:                                               *)
Safety == [] (state \in Nat /\ state <= Limit)

(* Liveness property: eventually reach the saturation value.         *)
Liveness == <> (state = Limit)

THEOREM SafetyTheorem  == Spec => Safety
THEOREM LivenessTheorem == Spec => Liveness

(* ------------------------------------------------------------------ *)
(* Invariant that captures the safety conditions.                     *)
Inv == state \in Nat /\ state <= Limit

THEOREM InvInit      == Init => Inv
THEOREM InvPreserved == [] ((Inv /\ Next) => Inv')

=============================================================================