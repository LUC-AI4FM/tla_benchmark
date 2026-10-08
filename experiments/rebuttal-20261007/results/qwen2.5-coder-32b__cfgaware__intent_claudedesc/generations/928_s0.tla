------------------------------- MODULE ClockEquivalence -------------------------------

EXTENDS HourClock

CONSTANTS HC, HC2

VARIABLE hour

HC == /\ hour \in 1..12
    /\ [][hour' = IF hour = 12 THEN 1 ELSE hour + 1]_<<hour>>

HC2 == /\ hour \in 1..12
     /\ [][hour' = (hour \% 12) + 1]_<<hour>>

THEOREM HC => HC2

THEOREM HC2 => HC

=============================================================================