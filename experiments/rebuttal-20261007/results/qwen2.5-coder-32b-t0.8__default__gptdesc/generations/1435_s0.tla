```tla
MODULE TrivialSystem

EXTENDS TLC

CONSTANTS 
    \* No constants defined in this module

VARIABLES 
    x

Init == x = 0

Next == TRUE

Spec == Init /\ [][Next]_<<x>>

\* Fairness conditions, if any, are not mentioned in the description
```