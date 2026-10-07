---- MODULE BoolToggle ----
EXTENDS TLC

CONSTANTS Dummy

VARIABLES x

Init == x = TRUE

Next == x' = ~x

vars == << x >>

Spec == Init /\ [][Next]_vars

TypeOK == x \in BOOLEAN
IsTrue == x = TRUE
IsFalse == x = FALSE

====