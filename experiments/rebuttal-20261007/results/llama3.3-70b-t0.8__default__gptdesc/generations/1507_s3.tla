```
MODULE TinySystem
EXTENDS Integers

CONSTANTS 

VARIABLES clock

Check(p) == IF p THEN TRUE ELSE FALSE

Flip(b) == ~b

TypeOK == clock \in {TRUE, FALSE}

Init == (/\
          clock = TRUE \
         )

Next == clock' = Flip(clock)

Spec == Init /\ [][Next]_clock

THEOREM Spec => []TypeOK
```