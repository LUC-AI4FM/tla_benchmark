------------------------------ MODULE PlusCalASTTranslation ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Object, Any

VARIABLES state

(* --------------------------------------------------------------------------- *)
(*  Translation operators for the abstract syntax tree of a PlusCal algorithm   *)
(* --------------------------------------------------------------------------- *)

Init == /\ state = [obj |-> Object]
Next == /\ state' = [obj |-> Any]

Spec == Init /\ [][Next]_state

Termination == state[obj] = Any

(* --------------------------------------------------------------------------- *)
(*  Fairness options (used only for documentation; not enforced by the spec)   *)
(* --------------------------------------------------------------------------- *)

NoFairness                == TRUE
WeakFairProcessActions    == FALSE
WeakFairNext              == FALSE
StrongFairProcessActions  == FALSE

===============================================================================