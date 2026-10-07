```
MODULE B
EXTENDS Integers

CONSTANTS 

VARIABLES x

Init == x = FALSE

Switch(x) == IF x THEN FALSE ELSE TRUE

A == x' = Switch(x)
B == x' = Switch(x)

Next == (A) \/ (B)

Spec == Init /\ [][Next]_

THEOREM Spec => []<>TRUE
```