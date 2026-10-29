---- MODULE test47 ----
EXTENDS test47a, Integers

VARIABLE x

vars == <<x>>

Init == x = -1

Next == IF x > -3
          THEN x' = x - 1
          ELSE UNCHANGED x

Spec == Init /\ [][Next]_vars

Inv == TRUE

TypeOK == x \in {-1, -2, -3}

====