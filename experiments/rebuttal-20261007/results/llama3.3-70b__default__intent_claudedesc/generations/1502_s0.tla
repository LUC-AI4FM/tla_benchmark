```
MODULE OperatorSubstitutionDemo
EXTENDS Integers, FiniteSets

CONSTANTS Op

VARIABLE x

Init == x = 0

Next == x' \in Op(x)

Spec == Init /\ [][Next]_x

THEOREM Spec => []x \in Nat
```