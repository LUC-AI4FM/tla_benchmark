MODULE SimpleEquality
EXTENDS Integers

VARIABLES x, y

(* --- Initialization --- *)
Init == /\ x = 0
        /\ y = 0
        /\ x = y

(* --- Next-state relation (stuttering only) --- *)
Next == /\ x' = x
        /\ y' = y

(* --- Specification --- *)
Spec == Init /\ [][Next]_<<x, y>>

(* --- Invariants --- *)
EqualityInvariant == x = y

(* --- Temporal properties --- *)
THEOREM EqualityInvariantHolds ==
  Spec => [] EqualityInvariant

===============================================================================