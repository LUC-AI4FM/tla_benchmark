---- MODULE CounterSpec ----
EXTENDS Naturals

CONSTANT Limit

VARIABLE x

Init == x = 0

Next == IF x < 3 THEN x' = x + 1 ELSE x' = x

Spec == Init /\ [][Next]_<<x>>

====