MODULE SmallModel
EXTENDS Naturals

VARIABLE s

Next ==
  /\ s' \in {0,1}
  /\ s' > 0

Init == s = 23

Inv == s # 0

Spec == Init /\ [][Next]_s

===============================================================================