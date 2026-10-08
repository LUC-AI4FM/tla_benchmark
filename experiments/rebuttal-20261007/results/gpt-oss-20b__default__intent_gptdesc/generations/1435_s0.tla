```
------------------------------ MODULE ConstantState ------------------------------
EXTENDS Naturals

VARIABLE state

(* --- Initialization --- *)
Init == state = 0

(* --- Next-state relation (no change) --- *)
Next == state' = state

(* --- Specification: infinite sequence of states --- *)
Spec == Init /\ [][Next]_state

(* --- Properties to check --- *)

(* 1. Initialization property: state equals zero in the initial state *)
InitProp == Init

(* 2. Safety invariant: state remains zero in all reachable states *)
SafetyInv == [] (state = 0)

(* 3. Liveness condition: time can advance indefinitely while preserving the invariant *)
LivenessCond == []<>(state = 0)
```