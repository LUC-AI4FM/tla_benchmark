---------------------------- MODULE SimpleClock ----------------------------

EXTENDS Integers, TLC

CONSTANTS 

VARIABLES hr

Init == 1 <= hr /\ hr <= 12

Next == 
    \/ (hr < 12) /\ (hr' = hr + 1)
    \/ (hr = 12) /\ (hr' = 1)

HC == Init /\ [] [][Next]_<<hr>>

Spec == HC

THEOREM HC => []Init

=============================================================================