---- MODULE TraceExploreNoErrorTest ----
EXTENDS Naturals

CONSTANT Limit

VARIABLES x

vars == <<x>>

Init == x = 0

Next == IF x < 3
           THEN x' = x + 1
           ELSE UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

====