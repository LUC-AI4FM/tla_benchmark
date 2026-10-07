------------------------------- MODULE BooleanFlipper -------------------------------

EXTENDS TLC

CONSTANTS Dummy

VARIABLES x

Init ==
  x = TRUE

Next ==
  x' = ~x

IsTrue ==
  x = TRUE

IsFalse ==
  x = FALSE

Spec ==
  Init /\ [][Next]_x

===============================================================================