MODULE SmallSetSystem
EXTENDS Naturals

CONSTANT Data

VARIABLE state

Init == 
  state = {}

Next ==
  /\ ∃ x \in Data :
       state' = state ∪ {x}

Spec ==
  Init /\ [][Next]_state

===============================================================================