---- MODULE ASetSpec ----
VARIABLE x

ASet == {f \in [{0} -> {0}] : x}

Spec == (x = TRUE) /\ [][x' = (ASet = {})]_x
====