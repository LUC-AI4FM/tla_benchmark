---- MODULE HourClock ----
EXTENDS Integers

VARIABLES hour

TypeInv == hour \in 1..12

Init == TypeInv

NextHour(h) == IF h \in 1..11 THEN h + 1 ELSE 1

Next == hour' = NextHour(hour)

vars == << hour >>

LSpec == Init /\ [][Next]_vars /\ WF_vars(Next)

AlwaysTick == []<>(<Next>_vars)

AllTimes == \A t \in 1..12 : []<>(hour = t)

TypeInvariance == []TypeInv
====