--------------------------- MODULE HourClock2 ---------------------------
EXTENDS Integers, HourClock

VARIABLE hr

HCini == (hr \in 1..12)

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCini /\ [][HCnxt2]_hr

THEOREM HC <=> HC2

=============================================================================