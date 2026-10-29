---- MODULE ExtendsTest ----
EXTENDS Naturals, Integers

VARIABLES x

vars == <<x>>

Init == x = -1

Next == IF x = -3
           THEN UNCHANGED x
           ELSE x' = x - 1

Spec == Init /\ [][Next]_vars

TypeOK == x \in {-1, -2, -3}

Inv == TRUE

====