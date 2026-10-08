---------------------------- MODULE Clock12Hour ----------------------------

VARIABLE hour

HC == 
    /\ hour \in 1..12
    /\ hour' = IF hour = 12 THEN 1 ELSE hour + 1

HCini == hour \in 1..12

Spec == HCini /\ [][HC]_hour

ValidHour == hour \in 1..12

THEOREM Spec => []ValidHour

=============================================================================