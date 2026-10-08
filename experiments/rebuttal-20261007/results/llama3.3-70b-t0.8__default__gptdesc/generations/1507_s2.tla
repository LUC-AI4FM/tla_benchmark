```tla
MODULE ClockSystem

EXTENDS Integers

CONSTANTS None

VARIABLES clock

Check(p) == IF p THEN TRUE ELSE FALSE

Flip(b) == IF b THEN FALSE ELSE TRUE

TypeOK == clock \in {TRUE, FALSE}

Init == (* TLC will explore all possible values of clock *)
        /\ clock = TRUE
        /\ Check(clock)

Next == clock' = Flip(clock)

Spec == Init /\ [][Next]_clock

THEOREM Spec => []TypeOK
```