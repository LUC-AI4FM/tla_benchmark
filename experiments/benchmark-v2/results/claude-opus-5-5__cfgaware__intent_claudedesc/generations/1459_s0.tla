---- MODULE TraceExpressionNoError ----
EXTENDS Naturals

CONSTANT Limit

VARIABLE x

vars == <<x>>

Init == x = 0

Next == \/ /\ x < Limit
           /\ x' = x + 1
        \/ /\ x >= Limit
           /\ UNCHANGED x

Spec == Init /\ [][Next]_vars

TypeOK == x \in 0..Limit
====