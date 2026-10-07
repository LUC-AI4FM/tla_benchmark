MODULE MinimalSystem
CONSTANT Op

VARIABLE x

Init == x = 0

Next == \/ x' \in Op(x)

Spec == Init /\ [][Next]_x

Id(n) == SUBSET {1,2,3}
Forty2 == Id