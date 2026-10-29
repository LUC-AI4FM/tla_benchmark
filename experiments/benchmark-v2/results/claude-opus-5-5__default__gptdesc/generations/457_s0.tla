---- MODULE ASetSpec ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>

ASet == {f \in [{0} -> {0}] : x}

Init == x = TRUE

Next == x' = (ASet = {})

Spec == Init /\ [][Next]_x

TypeOK == x \in BOOLEAN

====