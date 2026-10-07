------------------------------ MODULE HourClock2 ------------------------------

EXTENDS HourClock

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCini /\ [][HCnxt2]_hr

Init == HCini
Next == HCnxt2
Spec == HC2

TypeInv == hr \in 1..12

THEOREM HC <=> HC2

THEOREM Spec => []TypeInv

=============================================================================