------------------------------ MODULE SmallSet ------------------------------
EXTENDS SETS

CONSTANTS Data

VARIABLE state

Init ==
  /\ state = {}

Next ==
  \E e \in Data : state' = state ∪ {e}