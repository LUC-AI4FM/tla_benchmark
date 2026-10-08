---------------------------- MODULE SimpleState ----------------------------
EXTENDS Integers

CONSTANT Universe, Threshold
VARIABLE state

Init == 
  /\ state \in Universe
  /\ state > Threshold
  /\ BooleanCondition(state)

Next == 
  UNCHANGED state

BooleanCondition(val) == val mod 2 = 0

THEOREM Init => state \in Universe
THEOREM Init => state > Threshold
THEOREM Init => BooleanCondition(state)
=============================================================================