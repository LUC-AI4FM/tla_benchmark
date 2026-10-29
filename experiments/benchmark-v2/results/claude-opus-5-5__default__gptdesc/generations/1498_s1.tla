---- MODULE Switch ----
VARIABLE x

Init == x = FALSE

Switch(v) == ~v

A == x' = Switch(x)

B == x' = Switch(x)

Next == A \/ B

Spec == Init /\ [][Next]_x

TypeOK == x \in BOOLEAN
====