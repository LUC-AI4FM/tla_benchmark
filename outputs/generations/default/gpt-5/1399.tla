------------------------------ MODULE BoolFlipper ------------------------------

EXTENDS TLC

CONSTANTS
  Dummy

VARIABLES
  x

vars == << x >>

Init == x = TRUE

Next == x' = ~x

IsTrue == x = TRUE
IsFalse == x = FALSE
TypeInv == x \in BOOLEAN

Spec == Init /\ [][Next]_vars

=============================================================================