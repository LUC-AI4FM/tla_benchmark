```
MODULE SmallSystem
EXTENDS Integers

CONSTANTS 
  FSet == {1, 2, 3, 4, 5}
  NSet == {1, 2, 3}

VARIABLE x

F(i) == 
  IF i = 1 THEN 0 
  ELSE F(i-1) + 1

N(n, x) == 
  (n = 1) => (x' = x + 1)
  \/ (n = 2) => (x' = x * 2)
  \/ (n = 3) => (x' = x - 1)

Init == (x \in FSet)

Next == \E n \in NSet : N(n, x)

Spec == Init /\ [][Next]_x

Inv == x \in {F[i] : i \in FSet}

THEOREM Spec => []Inv
```