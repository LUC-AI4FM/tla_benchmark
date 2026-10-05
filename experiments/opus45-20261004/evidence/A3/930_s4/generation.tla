--------------------------- MODULE TwelveHourClock ---------------------------
EXTENDS Naturals

VARIABLES hr

HCini == hr \in (1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HC == HCini /\ [][HCnxt]_hr

Init == HCini

Next == HCnxt

Spec == HC

TypeInvariant == hr \in (1..12)

THEOREM HC => []HCini

=============================================================================