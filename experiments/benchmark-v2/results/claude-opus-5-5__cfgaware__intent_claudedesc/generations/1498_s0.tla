---- MODULE BooleanToggle ----
VARIABLE b

vars == << b >>

Neg(x) == ~x

TypeOK == b \in BOOLEAN

Init == b = FALSE

A == b' = Neg(b)

B == b' = Neg(b)

Next == A \/ B

Spec == Init /\ [][Next]_vars
====