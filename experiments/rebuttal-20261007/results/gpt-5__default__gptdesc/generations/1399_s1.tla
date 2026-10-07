--------------------------- MODULE BooleanFlipper ---------------------------
EXTENDS TLC

CONSTANTS UNUSED

VARIABLES x

IsTrue == x = TRUE
IsFalse == x = FALSE

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x
=============================================================================