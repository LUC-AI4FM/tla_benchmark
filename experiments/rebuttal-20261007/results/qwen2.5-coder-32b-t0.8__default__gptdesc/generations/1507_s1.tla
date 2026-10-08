```tla
MODULE TinyClock

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    \* No constants needed for this simple system

VARIABLES clock

Check(b) == \/ b = TRUE \/ b = FALSE
Flip(b)  == IF b THEN FALSE ELSE TRUE

Init == Check(clock)

Next == clock' = Flip(clock)

Spec == /\ Init
        /\ [][Next]_<<clock>>
        /\ WF_next(<<clock>>)

INVARIANT Check(clock)
```