---------------------------- MODULE CountToFive ----------------------------
EXTENDS Naturals

VARIABLE x

vars == <<x>>

Init == x = 1

Next == IF x < 5
           THEN x' = x + 1
           ELSE x' = x

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety invariants
TypeOK == x \in Nat

InRange == x \in 1..5

\* Liveness: from the initial value x = 1, the system eventually
\* reaches x = 5 and thereafter always remains at x = 5.
Liveness == (x = 1) => <>[](x = 5)

\* Equivalent leads-to formulation
EventuallyStable == (x = 1) ~> [](x = 5)

THEOREM Spec => []TypeOK
THEOREM Spec => []InRange
THEOREM Spec => Liveness
=============================================================================