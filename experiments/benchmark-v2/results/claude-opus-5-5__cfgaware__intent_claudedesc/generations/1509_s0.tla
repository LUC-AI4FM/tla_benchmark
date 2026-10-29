---- MODULE RecursiveFunctionInv ----
EXTENDS Naturals

Dom == 0..5

\* Recursive function: triangular numbers (f[0] = 0, f[n] = f[n-1] + n)
f[n \in Dom] == IF n = 0 THEN 0 ELSE f[n-1] + n

Range == {f[n] : n \in Dom}

VARIABLE x

vars == <<x>>

Init == x = f[3]

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

Inv == \E n \in Dom : x = f[n]

TypeOK == x \in Range
====