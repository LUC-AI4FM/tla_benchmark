```
MODULE SingleVariableInitialization
EXTENDS Integers

CONSTANTS 

VARIABLES s

Init == (\E x \in (0..1) : s = x /\ s < 1)

Next == UNCHANGED s

Inv == s < 1

Spec == Init /\ [][Next]_s

THEOREM Spec => []Inv
```
Note: This TLA+ specification assumes that the `UNCHANGED` operator is used to express that variable `s` does not change over time. The temporal formula `[][Next]_s` asserts that `Next` holds for all steps and applies only to variable `s`.