```
MODULE SimpleAssertion
EXTENDS Integers

CONSTANTS 

VARIABLES x, done

Init == (x \in 1..10) /\ done = FALSE

Next == IF ~done 
        THEN (x' = x) /\ (done' = (x * x <= 100))
        ELSE (x' = x) /\ (done' = done)

Spec == Init /\ [][Next]_<<x, done>>
Termination == <>(done = TRUE)

THEOREM Spec => []Termination
```