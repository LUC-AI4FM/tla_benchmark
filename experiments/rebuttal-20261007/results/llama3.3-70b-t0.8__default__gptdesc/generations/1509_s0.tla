```
MODULE SmallSystem
EXTENDS Integers

CONSTANTS 
  FVal

VARIABLES x

F[1] == 2
F[n \in {2,3,4,5}] == IF n = 5 THEN 1 ELSE F[n + 1]

N[i \in {1,2,3}, x'] == 
  (i = 1 /\ x' = F[x]) \/ 
  (i = 2 /\ x' = x) \/
  (i = 3 /\ x' = x)

Inv == x \in {1,2,3,4,5}

Init == x = 1

Next == \E i \in {1,2,3} : N[i, x']

Spec == Init /\ [][Next]_x

THEOREM Spec => []Inv
```