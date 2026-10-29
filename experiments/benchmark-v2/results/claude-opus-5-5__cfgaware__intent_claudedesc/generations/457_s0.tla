---- MODULE BoolFcnSetFilter ----
VARIABLE b

Init == b = TRUE

Next == b' = ({f \in [{0} -> {0}] : b} = {})

Spec == Init /\ [][Next]_b
====