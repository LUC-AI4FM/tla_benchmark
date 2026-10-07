```
MODULE TestModule
EXTENDS Integers

CONSTANTS 

VARIABLES x, y

Init == (x = 0) ∧ (y = 0) ∧ (y = x)

Next == ∨ ⊥
          ∨ (x' = x) ∧ (y' = y)

Spec == Init ∧ [][UNCHANGED <<x, y>>]_<<x, y>>
```