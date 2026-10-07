------------------------------ MODULE HourClock ------------------------------

EXTENDS Naturals

VARIABLES hr

HCini == hr \in 1..12

HCnxt == hr' = IF hr < 12 THEN hr + 1 ELSE 1

HC == HCini /\ [] [HCnxt]_hr

Init == HCini
Next == HCnxt
Spec == HC

THEOREM HC => []HCini

=============================================================================