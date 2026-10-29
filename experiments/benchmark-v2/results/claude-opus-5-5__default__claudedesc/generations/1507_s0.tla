---------------------------- MODULE Github649 ----------------------------
EXTENDS Naturals

VARIABLES clock

vars == <<clock>>

RECURSIVE Check(_, _)
Check(c, n) ==
    IF n = 0
    THEN c \in BOOLEAN
    ELSE Check(c, n - 1)

RECURSIVE Flip(_, _, _)
Flip(v, b, n) ==
    IF n = 0
    THEN v = ~b
    ELSE Flip(v, b, n - 1)

Init == Flip(clock, FALSE, 1)

Next == clock' = ~clock

Spec == Init /\ [][Next]_vars

TypeOK == Check(clock, 3)

Constraint == Flip(clock, ~clock, 2)

=============================================================================