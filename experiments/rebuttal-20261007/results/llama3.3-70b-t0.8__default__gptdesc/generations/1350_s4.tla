```
MODULE Incrementer
EXTENDS Integers

CONSTANTS

VARIABLES x

Init == (x = 1)

Next == IF x < 5 THEN x' = x + 1 ELSE x' = x

Spec == Init /\ [][Next]_x
          /\ WF_x(Next)

THEOREM Spec => <>[]x = 5
```