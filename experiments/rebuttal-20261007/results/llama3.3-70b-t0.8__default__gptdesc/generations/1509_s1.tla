```
MODULE SmallSystem
EXTENDS Integers

CONSTANTS

VARIABLES x

F(a) == IF a = 1 THEN 2 ELSE F(a-1) + 1

N(i, x) == x' = IF i = 1 THEN x + 1
               ELSE IF i = 2 THEN x * 2
               ELSE x - 1

Inv == x \in {1, 2, 3, 4, 5}

Init == x = 1

Next == \E i \in {1,2,3} : N(i, x)

Spec == Init /\ [][Next]_x

THEOREM Spec => []Inv
```