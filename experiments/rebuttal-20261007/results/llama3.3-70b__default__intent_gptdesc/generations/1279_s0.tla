```
MODULE SimpleSystem
EXTENDS Integers

CONSTANTS AllowedValues
VARIABLES x

Init == x = 5

Next == 
  \/ x' = x  \* stuttering step
  \/ (x' \in AllowedValues) /\ (x' > 0)

Spec == Init /\ [][Next]_x

Inv == x # 0

THEOREM Spec => []Inv
THEOREM Spec => <><> (x' \in AllowedValues) /\ (x' > 0)
```
Note: The `AllowedValues` constant set should be defined with the specific finite set of values, for example, `AllowedValues == {1, 2, 3}`.