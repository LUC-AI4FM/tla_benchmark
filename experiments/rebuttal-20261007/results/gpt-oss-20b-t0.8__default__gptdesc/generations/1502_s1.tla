MODULE SmallSM

CONSTANT Op

VARIABLE x

Init == 
  x = 0

Next ==
  \E y \in Op(x) : x' = y

Helper1 ==
  Op(x) \subseteq {0,1,2}

Helper2 ==
  {x} \subseteq Op(x)

Spec ==
  Init /\ [][Next]_x