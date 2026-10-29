---- MODULE BoolClock ----
EXTENDS Naturals

VARIABLE clock

vars == <<clock>>

RECURSIVE InitClock(_)
InitClock(n) ==
    IF n = 0
    THEN clock \in BOOLEAN
    ELSE InitClock(n - 1)

RECURSIVE ConstraintRec(_)
ConstraintRec(n) ==
    IF n = 0
    THEN clock \in BOOLEAN
    ELSE ConstraintRec(n - 1)

RECURSIVE IsBool(_, _)
IsBool(v, n) ==
    IF n = 0
    THEN v \in BOOLEAN
    ELSE IsBool(v, n - 1)

Init == InitClock(3)

Next == clock' = ~clock

Spec == Init /\ [][Next]_vars

TypeOK == IsBool(clock, 2)

Constraint == ConstraintRec(2)

====