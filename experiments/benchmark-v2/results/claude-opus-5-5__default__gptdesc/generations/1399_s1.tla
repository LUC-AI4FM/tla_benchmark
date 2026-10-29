---- MODULE BooleanFlip ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>

TypeOK == x \in BOOLEAN

IsTrue == x = TRUE

IsFalse == x = FALSE

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

====