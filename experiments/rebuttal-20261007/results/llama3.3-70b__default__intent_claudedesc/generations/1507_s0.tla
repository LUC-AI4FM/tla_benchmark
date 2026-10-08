```
MODULE BooleanClock
EXTENDS Integers

CONSTANTS None

VARIABLES clock

Init == clock = TRUE

Next == clock' = ~clock

Spec == Init /\ [][Next]_clock

TypeInvariant == clock \in {TRUE, FALSE}

THEOREM Spec => []TypeInvariant
```