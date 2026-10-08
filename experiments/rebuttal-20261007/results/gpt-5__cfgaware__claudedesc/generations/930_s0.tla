------------------------------ MODULE HourClock ------------------------------
EXTENDS Integers

VARIABLES hr

HCini ==
    hr \in 1..12

HCnxt ==
    (hr # 12 /\ hr' = hr + 1)
    \/ (hr = 12 /\ hr' = 1)

HC ==
    HCini /\ [][HCnxt]_hr

THEOREM HC => []HCini
=============================================================================