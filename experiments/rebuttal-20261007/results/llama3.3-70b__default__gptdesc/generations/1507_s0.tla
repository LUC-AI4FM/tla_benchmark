```
MODULE ClockSystem
EXTENDS Integers

CONSTANTS 

VARIABLES clock

Check(p) == IF p THEN TRUE ELSE FALSE

Flip(b) == IF b THEN FALSE ELSE TRUE

TypeOK == clock \in {TRUE, FALSE}

Init == (* TLC will check this recursive call *)
        /\ Check(clock = TRUE)
        /\ clock = TRUE

StatePredicate == clock = TRUE

Next == clock' = Flip(clock)

Spec == Init /\ [][Next]_clock

THEOREM Spec => []TypeOK
THEOREM Spec => <>[]StatePredicate
```