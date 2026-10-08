```
MODULE SmallSystem
EXTENDS Integers

CONSTANTS 

VARIABLES x

F[n \in {1,2,3,4,5}] == 
  IF n = 1 THEN 0
  ELSE F[n-1] + 1

N[i \in {1,2,3}, x] == 
  /\ x' = x + i
  /\ x < 10

Init == x = 0

Next == \E i \in {1,2,3} : N[i, x]

Spec == Init /\ [][Next]_x

Inv == x \in {F[n] : n \in {1,2,3,4,5}}

THEOREM Spec => []Inv
```