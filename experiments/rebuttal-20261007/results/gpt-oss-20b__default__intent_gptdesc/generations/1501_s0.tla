MODULE CounterFactorial
EXTENDS Naturals

(* Factorial constants *)
FACT3 == 6
FACT9 == 362880

VARIABLE counter

Init == counter = 0

ShortUpdate == counter' = FACT3
LongUpdate   == counter' = FACT9

Next == ShortUpdate \/ LongUpdate

SafetyInvariant == counter ∈ {FACT3, FACT9}

Spec == Init /\ [][Next]_counter

(* Liveness: the system never deadlocks *)
NoDeadlock == [] (ShortUpdate \/ LongUpdate)

END MODULE