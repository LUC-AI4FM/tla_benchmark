```tla
MODULE RandomSample

EXTENDS Integers, FiniteSets

CONSTANTS 
    S \* A finite set of nine integers
    T \* The integer range 1..10

VARIABLES x

Init == x \in RandomSubset(1000, [S -> T])

Next == TRUE

Spec == Init /\ [][Next]_<<x>>

Inv == TRUE

(* Fairness conditions are not mentioned, so they are omitted *)
```