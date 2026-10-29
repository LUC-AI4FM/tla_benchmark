---- MODULE BooleanToggle ----
EXTENDS Naturals

VARIABLE b

vars == << b >>

TypeOK == b \in BOOLEAN

Negate(x) == ~x

Init == b = FALSE

A == b' = Negate(b)

B == b' = Negate(b)

Next == A \/ B

Spec == Init /\ [][Next]_vars

====