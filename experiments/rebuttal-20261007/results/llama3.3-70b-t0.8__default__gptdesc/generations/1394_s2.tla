```
MODULE Github702
EXTENDS Integers
CONSTANTS 
VARIABLES y, z

fizzbuzz == 2

Init == (y \in {1,2,3}) /\ (z \in {1,2,3})

Next == y' = y + 1 /\ z' = z

Spec == Init /\ [][Next]_<<y, z>>

x_unchanged(y, z) == 
  INSTANCE x_unchanged_template WITH x <- fizzbuzz, y <- y, z <- z

MODULE x_unchanged_template
EXTENDS Integers
CONSTANTS 
VARIABLES x, y, z

Init == (x \in {1,2,3}) /\ (y \in {1,2,3}) /\ (z \in {1,2,3})

Next == y' = y + 1 /\ x' = x /\ z' = z

Spec == Init /\ [][Next]_<<x, y, z>>
```