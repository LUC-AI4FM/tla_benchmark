------------------------------- MODULE Github649 -------------------------------
EXTENDS Naturals

CONSTANTS 
    \* No constants needed for this specification

VARIABLES clock

Check(c, n) == IF n = 0 THEN c \in BOOLEAN ELSE Check(c, n - 1)
Flip(v, b, n) == IF n = 0 THEN v = ~b ELSE Flip(v, b, n - 1)

Init == Flip(clock, FALSE, 1)

Next == clock' = ~clock

TypeOK == Check(clock, 2)

Constraint == Flip(clock, ~clock, 2)

Spec == 
    /\ Init
    /\ [][Next]_<<clock>>
    /\ WF_next(<<clock>>)
    /\ TypeOK
    /\ Constraint

=============================================================================