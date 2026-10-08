----------------------------- MODULE IncrementStutter -----------------------------
EXTENDS Naturals

VARIABLE x

Init == x = 0

Next ==
    IF x < 3 THEN
        x' = x + 1
    ELSE
        x' = x

Spec == Init /\ [][Next]_x
=============================================================================