```
MODULE SmallSystem
EXTENDS Integers

CONSTANTS 
  XSet == {1,2,3,4,5}

VARIABLES x

F(n) == IF n = 1 THEN 2 ELSE F(n-1) + 1

N(i, x) == EXISTS y \in XSet : x' = y

Init == x \in XSet

Next == \E i \in {1,2,3} : N(i, x)

Inv == x \in {F(1), F(2), F(3), F(4), F(5)}

Spec == Init /\ [][Next]_x
```