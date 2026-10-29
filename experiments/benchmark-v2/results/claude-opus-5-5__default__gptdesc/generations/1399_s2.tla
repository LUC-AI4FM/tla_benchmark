---- MODULE BooleanFlip ----
EXTENDS Naturals

VARIABLES x

vars == << x >>

TypeOK == x \in BOOLEAN

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

IsTrue == x = TRUE

IsFalse == x = FALSE

====