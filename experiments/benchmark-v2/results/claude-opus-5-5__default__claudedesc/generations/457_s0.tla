---- MODULE SetFilterTest ----
EXTENDS Naturals

VARIABLES x

vars == <<x>>

ASet == {f \in [{0} -> {0}] : x}

TypeOK == x \in BOOLEAN

Init == x = TRUE

Next == x' = (ASet = {})

Spec == Init /\ [][Next]_x

====