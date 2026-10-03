--------------------------- MODULE HourClock ---------------------------

EXTENDS Integers

CONSTANTS Hrs
ASSUME Hrs = 1..12

VARIABLES hr

HCini == hr \in Hrs

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

Init == HCini

Next == HCnxt

Spec == Init /\ [][Next]_hr

HC == HCini /\ [][HCnxt]_hr

THEOREM HCInv == HC => []HCini

============================================================================