MODULE BooleanClock
EXTENDS Naturals, TLC

VARIABLES clock

InitRec(n) ==
    IF n = 0 THEN FALSE ELSE NOT InitRec(n-1)

TypeCheckRec(b, k) ==
    IF k = 0 THEN b IN {TRUE, FALSE}
    ELSE (b IN {TRUE, FALSE} /\ TypeCheckRec(b, k-1))

Init == /\ clock = InitRec(3)

Next == /\ clock' = NOT clock

Spec == Init /\ [][Next]_clock /\ [] (TypeCheckRec(clock, 5))