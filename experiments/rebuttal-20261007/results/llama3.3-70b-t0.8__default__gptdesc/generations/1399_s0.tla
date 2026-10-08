```
MODULE OneVariableBooleanStateMachine
EXTENDS Integers

CONSTANTS 

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

THEOREM Spec => []Init
THEOREM Spec => <><>~x
```
Note: I used `<>` for "eventually" and `[]` for "always", as per standard TLA+ syntax. The `_x` subscript on `[Next]_x` indicates that the next-state relation is stuttering with respect to variable `x`. The two THEOREM statements are simple examples of safety and liveness properties, respectively.