---------------------------- MODULE CountToFive ----------------------------
EXTENDS Naturals

VARIABLES x

vars == <<x>>

TypeOK == x \in Nat

Init == x = 1

Increment == /\ x < 5
             /\ x' = x + 1

Stutter == /\ x = 5
           /\ UNCHANGED x

Next == Increment \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety invariants
RangeInv == x \in 1..5

\* Liveness: starting from x = 1, x eventually becomes 5 and stays there
Liveness == (x = 1) => <>[](x = 5)

EventuallyFive == <>(x = 5)

THEOREM Spec => []TypeOK
THEOREM Spec => []RangeInv
THEOREM Spec => Liveness
=============================================================================