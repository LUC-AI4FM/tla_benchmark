```
MODULE IncrementingVariable
EXTENDS Integers

CONSTANTS None

VARIABLES x

Init == (x = 1)

Next == IF x < 5 THEN x' = x + 1 ELSE x' = x

Spec == Init /\ [][Next]_x

Fairness == WF_x(Next)

Theorem == Spec => <>[]x = 5
```