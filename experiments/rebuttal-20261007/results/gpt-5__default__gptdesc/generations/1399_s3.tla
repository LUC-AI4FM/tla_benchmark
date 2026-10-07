---- MODULE BooleanFlipper ----
EXTENDS TLC

CONSTANTS Dummy

VARIABLES x

Init == x = TRUE

Next == x' = ~x

IsTrue == x = TRUE
IsFalse == x = FALSE
TypeOK == x \in BOOLEAN
Stutter == UNCHANGED x

Spec == Init /\ [][Next]_x

====