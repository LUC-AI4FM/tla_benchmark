------------------------------ MODULE HourClock ------------------------------

EXTENDS Integers

VARIABLES hour

HCini == hour \in 1..12

Next == hour' = IF hour # 12 THEN hour + 1 ELSE 1

ValidHour == hour \in 1..12

HC == HCini /\ [][Next]_hour

THEOREM HC => []ValidHour

=============================================================================