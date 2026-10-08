```
MODULE Github702
EXTENDS Integers
CONSTANTS 
VARIABLES y, z

fizzbuzz == 1

Instance_x_unchanged == INSTANCE x_unchanged WITH x <- fizzbuzz

Init == (y \in {1,2,3}) ∧ (z \in {1,2,3})

Next == y' = y + 1 ∧ z' = z ∧ Instance_x_unchanged!Next

Spec == Init ∧ [][Next]_<<y, z>>

=============================================================================
MODULE x_unchanged
EXTENDS Integers
CONSTANTS 
VARIABLES x, y, z

Init == (x \in {1,2,3}) ∧ (y \in {1,2,3}) ∧ (z \in {1,2,3})

Next == y' = y + 1 ∧ x' = x ∧ z' = z

Spec == Init ∧ [][Next]_<<x, y, z>>
```