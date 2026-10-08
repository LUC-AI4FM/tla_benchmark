------------------------------ MODULE ConstantState ------------------------------
EXTENDS Naturals

VARIABLE state

(* --- Initial condition ----------------------------------------------------- *)
Init == state = 0

(* --- Next-state relation (no change allowed) --------------------------------- *)
Next == state' = state

(* --- Specification: initial state followed by any number of no-op steps --------- *)
Spec == Init /\ [][Next]_state

(* --- Invariant property ------------------------------------------------------ *)
Inv == state = 0

(* --- Safety invariant: the state is always zero ------------------------------ *)
Safety == []Inv

(* --- Liveness condition: time can advance indefinitely while preserving the invariant *)
Liveness == []<>(TRUE)

===============================================================================