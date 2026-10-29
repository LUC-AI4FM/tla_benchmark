---- MODULE TraceExprNoError ----
EXTENDS Naturals

CONSTANT Bound

ASSUME Bound \in Nat

VARIABLE x

vars == <<x>>

Init == x = 0

Next == \/ /\ x < Bound
           /\ x' = x + 1
        \/ /\ x >= Bound
           /\ UNCHANGED x

Spec == Init /\ [][Next]_vars

TypeOK == x \in 0..Bound

BoundNeverExceeded == x <= Bound

====