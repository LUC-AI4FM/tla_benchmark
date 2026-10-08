MODULE TrivialInitial
EXTENDS TLA+

VARIABLE x, y

Init ==
  /\ x = 0
  /\ y = 0
  /\ x = y

Next ==
  /\ x' = x
  /\ y' = y

Spec == Init /\ [][Next]_{<<x,y>>}