```
MODULE OneVariableBooleanStateMachine
EXTENDS Integers

CONSTANTS 

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

THEOREM Spec => []Init
THEOREM Spec => <>[]~x
THEOREM Spec => <><>x
```
Note: The above code uses the common TLA+ convention of using a primed variable (e.g., `x'`) to denote the value of that variable in the next state. The `_` symbol is used to specify the variables that the action `Next` depends on, allowing for stuttering steps where the value of `x` does not change.