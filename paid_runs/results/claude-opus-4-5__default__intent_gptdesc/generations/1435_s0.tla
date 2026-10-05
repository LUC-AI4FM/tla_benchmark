---------------------------- MODULE ConstantState ----------------------------
EXTENDS Integers

VARIABLES state

(* Type invariant for the state variable *)
TypeOK == state \in Int

(* The state is always zero - core invariant *)
StateIsZero == state = 0

(* Initial state: state equals zero *)
Init == state = 0

(* Next state relation: state remains unchanged (stuttering only) *)
(* This explicitly prevents any transition that would change the state *)
Next == state' = state

(* The specification allows infinite stuttering while preserving the invariant *)
(* No fairness conditions are imposed since we don't require progress *)
Spec == Init /\ [][Next]_state

(* ========================