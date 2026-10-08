```
MODULE SmallSystem
EXTENDS Integers

CONSTANTS 
  FSet == {1,2,3,4,5}
  NSet == {1,2,3}

VARIABLE x

F(i) == 
  IF i = 1 THEN 0 
  ELSE F(i-1) + 1

N(i, x) == 
  (i = 1 /\ x' = x + 1) 
  \/ (i = 2 /\ x' = x * 2) 
  \/ (i = 3 /\ x' = x - 1)

Inv == x \in {F[i] : i \in FSet}

Init == x = F[1]

Next == \E i \in NSet : N(i, x)

Spec == Init /\ [][Next]_x

THEOREM Spec => []Inv
```