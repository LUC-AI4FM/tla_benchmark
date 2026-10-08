----------------------------- MODULE SimpleClock -----------------------------

EXTENDS Integers

CONSTANTS 

VARIABLES hr

Init == \/ hr = 1 
        \/ hr = 2 
        \/ hr = 3 
        \/ hr = 4 
        \/ hr = 5 
        \/ hr = 6 
        \/ hr = 7 
        \/ hr = 8 
        \/ hr = 9 
        \/ hr = 10
        \/ hr = 11
        \/ hr = 12

Next == IF hr < 12 THEN hr' = hr + 1 ELSE hr' = 1

HCini == Init

HCnxt == Next

HC == HCini /\ [][HCnxt]_<<hr>>

Spec == Init /\ WF_next(<<hr>>)

THEOREM HC => [](HCini)
=============================================================================