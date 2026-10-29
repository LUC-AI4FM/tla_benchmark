---- MODULE Switch ----
VARIABLE x

Switch(v) == ~v

Init == x = FALSE

A == x' = Switch(x)

B == x' = Switch(x)

Next == A \/ B

Spec == Init /\ [][Next]_x

TypeOK == x \in BOOLEAN
====