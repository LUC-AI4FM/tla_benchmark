------------------------------ MODULE CounterToFive ------------------------------

EXTENDS Naturals, Integers

CONSTANTS Dummy

VARIABLES x

vars == << x >>

Init == x = 1

Next == IF x < 5 THEN x' = x + 1 ELSE x' = x

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

SafetyInv == x \in 1..5

Liveness == <>[](x = 5)

THEOREM Spec => []SafetyInv

THEOREM Spec => Liveness

===============================================================================