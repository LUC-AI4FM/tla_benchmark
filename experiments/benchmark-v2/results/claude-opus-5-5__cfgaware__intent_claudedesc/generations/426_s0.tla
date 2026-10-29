---- MODULE MinimalSpec ----
EXTENDS Naturals

VARIABLE x

vars == << x >>

Init == x = 0

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

TypeOK == x \in Nat

====