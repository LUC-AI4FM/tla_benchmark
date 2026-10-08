------------------------------ MODULE GrowingSet ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Universe

VARIABLES S

(* --- Initial state ----------------------------------------------------- *)
Init == S = {}

(* --- One-step transition: nondeterministically add one element from the
      universe that is not already in the set. --------------------------------- *)
AddOne(x) ==
  /\ x \in Universe
  /\ x \notin S
  /\ S' = S \cup {x}

Next == \E x \in Universe : AddOne(x)

(* --- Full specification --------------------------------------------------- *)
Spec == Init /\ [][Next]_S

=============================================================================