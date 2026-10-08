```
MODULE Github702
EXTENDS Integers
CONSTANTS 
VARIABLES y, z

fizzbuzz == 1

Init == (y \in {1,2,3}) /\ (z \in {1,2,3})

Next == y' = y + 1 /\ z' = z

Spec == Init /\ [][Next]_<<y, z>>

x_unchanged == INSTANCE x_unchanged WITH x <- fizzbuzz

THEOREM Spec => []((y # 4) => (z = 1))

================================================================================================
MODULE x_unchanged
EXTENDS Integers
CONSTANTS 
VARIABLES x, y, z

Init == (x \in {1,2,3}) /\ (y \in {1,2,3}) /\ (z \in {1,2,3})

Next == y' = y + 1 /\ x' = x /\ z' = z

Spec == Init /\ [][Next]_<<x, y, z>>
```