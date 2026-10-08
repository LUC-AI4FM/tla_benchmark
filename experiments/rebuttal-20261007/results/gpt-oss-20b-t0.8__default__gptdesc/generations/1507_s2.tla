------------------------------ MODULE TinyClock ------------------------------
VARIABLES clock

(* Recursive operator definitions *)
Check(b) == b \in BOOLEAN
Flip(b) == NOT b

(* Type predicate using Check *)
TypePred == Check(clock)

(* Initial state predicate, uses Check and Flip *)
Init == TypePred /\ clock = FALSE
(* Note: The recursive operator call in Init may lead to coverage issues for TLC. *)

(* Constraint-like state predicate (safety invariant) *)
SafetyInv == TypePred

(* Transition: flip the clock value *)
Next == /\ clock' = Flip(clock)

Spec == Init /\ [][Next]_clock

=============================================================================