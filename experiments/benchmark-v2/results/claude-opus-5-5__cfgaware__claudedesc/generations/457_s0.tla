---- MODULE ASetTest ----
VARIABLE x

ASet == {f \in [{0} -> {0}] : x}

Init == x = TRUE

Next == x' = (ASet = {})

Spec == Init /\ [][Next]_x
====