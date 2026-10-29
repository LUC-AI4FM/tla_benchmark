------------------------------ MODULE CountToFive ------------------------------
EXTENDS Naturals

VARIABLE x

vars == <<x>>

TypeOK == x \in Nat

Init == x = 1

Next == IF x < 5
           THEN x' = x + 1
           ELSE x' = x

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: x always stays within the range 1..5
RangeInv == x \in 1..5

\* Liveness: from x = 1, the system eventually reaches x = 5 and stays there forever
Liveness == (x = 1) ~> [](x = 5)

THEOREM Spec => []TypeOK
THEOREM Spec => []RangeInv
THEOREM Spec => Liveness
=============================================================================