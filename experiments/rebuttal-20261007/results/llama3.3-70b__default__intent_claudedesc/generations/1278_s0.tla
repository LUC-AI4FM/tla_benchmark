```
MODULE EvenVariable
EXTENDS Integers

CONSTANTS 

VARIABLES x

Init == (x = 0)

Next == (x' = x) OR (x' \in {i \in 0..9 : i % 2 = 0})

Spec == Init /\ [][Next]_x

THEOREM Spec => []Init
```