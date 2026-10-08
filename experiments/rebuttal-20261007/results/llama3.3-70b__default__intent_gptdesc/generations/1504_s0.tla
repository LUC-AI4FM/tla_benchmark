```
MODULE SimpleReactiveSystem
EXTENDS Integers

CONSTANTS 

VARIABLES boolState

Init == boolState = TRUE

Next == (* stuttering step *)
        boolState' = boolState

Spec == Init /\ [][Next]_boolState

THEOREM Spec => []boolState = TRUE
THEOREM Spec => <>[]<>(Next)
```
Note: The above TLA+ specification uses the `THEOREM` keyword to state the safety and liveness properties as separate theorems, which can be verified using the TLC model checker. 

However, a more idiomatic way of writing this in TLA+ would use the `INVARIANT` and `LIVENESS` keywords (or temporal logic operators) directly within the specification:

```
MODULE SimpleReactiveSystem
EXTENDS Integers

CONSTANTS 

VARIABLES boolState

Init == boolState = TRUE

Next == (* stuttering step *)
        boolState' = boolState

Spec == Init /\ [][Next]_boolState
          /\ INVARIANT boolState = TRUE
          /\ LIVENESS <>[]<>(Next)
```
Or using temporal logic operators:

```
MODULE SimpleReactiveSystem
EXTENDS Integers

CONSTANTS 

VARIABLES boolState

Init == boolState = TRUE

Next == (* stuttering step *)
        boolState' = boolState

Spec == Init /\ [][Next]_boolState
          /\ [](boolState = TRUE)
          /\ <>[]<>(Next)
```
Note that the `INVARIANT` and `LIVENESS` keywords are not standard TLA+ but can be used in certain verification tools for clarity. Temporal logic operators (`[]`, `<>`) provide a more traditional way to express these properties directly within the specification.