```
MODULE SimpleSystem
EXTENDS Integers

CONSTANTS 

VARIABLES s

Init == (s = 0)

Next == IF s' = s THEN TRUE 
        ELSE (s' >= 0) ∧ (s' <= 9) ∧ (s' % 2 = 0)

Spec == Init ∧ [][Next]_s
```