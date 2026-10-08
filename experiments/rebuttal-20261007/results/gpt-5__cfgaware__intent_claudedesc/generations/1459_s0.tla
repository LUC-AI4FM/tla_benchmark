---- MODULE Counter ----
EXTENDS Naturals

CONSTANT Limit

VARIABLE cnt

Init == cnt = 0

Next ==
  \/ /\ cnt < Limit
     /\ cnt' = cnt + 1
  \/ /\ cnt = Limit
     /\ cnt' = cnt

Spec == Init /\ [][Next]_cnt

====