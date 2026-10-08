```
MODULE Clock
EXTENDS Integers

CONSTANTS

VARIABLES clock

Check(p) == IF p THEN TRUE ELSE FALSE

Flip(b) == ~b

TypeOK == clock \in {TRUE, FALSE}

Init == (/* TLC will not check the following line due to recursive operator call */ 
          Check(clock = TRUE) /\ 
          clock = TRUE)

Next == clock' = Flip(clock)

Spec == Init /\ [][Next]_clock

THEOREM Spec => []TypeOK
```