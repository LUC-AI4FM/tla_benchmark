---- MODULE BoolFlip ----
EXTENDS Naturals

VARIABLE x

vars == << x >>

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

TypeOK == x \in BOOLEAN

IsTrue == x = TRUE

IsFalse == x = FALSE

Prop == x \in BOOLEAN

====