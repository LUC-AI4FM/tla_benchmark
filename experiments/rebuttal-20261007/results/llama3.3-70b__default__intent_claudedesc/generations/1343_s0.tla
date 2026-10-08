```
MODULE ConjunctiveInit
EXTENDS Integers

CONSTANTS 

VARIABLES x, y

Init == (y = 0) ∧ (x = 0) ∧ (y = x)

Next == (x' = x) ∧ (y' = y)

Spec == Init ∧ [][Next]_<<x, y>>
  
THEOREM Spec => []((x = 0) ∧ (y = 0))
```