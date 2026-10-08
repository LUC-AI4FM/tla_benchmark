------------------------------ MODULE FactorialCounter ------------------------------
VARIABLE counter

CONSTANTS
  ShortFact,
  LongFact

(* --- Initial state ----------------------------------------------------------- *)
Init == counter = 0

(* --- Actions --------------------------------------------------------------- *)
ShortUpdate ==
  /\ counter' = ShortFact

LongUpdate ==
  /\ counter' = LongFact

Next == ShortUpdate \/ LongUpdate

(* --- Specification ---------------------------------------------------------- *)
Spec == Init /\ [][Next]_counter

(* --- Safety invariant ------------------------------------------------------- *)
Inv == counter ∈ {ShortFact, LongFact}

(* --- Liveness properties (informal) ---------------------------------------- *)
NoDeadlock == [] (ShortUpdate \/ LongUpdate)

WF_Updates == WF_vars(ShortUpdate) /\ WF_vars(LongUpdate)
===============================================================================