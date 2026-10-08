------------------------------ MODULE Inner ------------------------------
VARIABLE x

Init == x = 0

incStep == IF x < 3 THEN x' = x + 1 ELSE FALSE

Next == incStep
-----------------------------------------------------------------------

------------------------------ MODULE Outer ------------------------------
EXTENDS Naturals

VARIABLES outerX

INSTANCE Inner(x=outerX)

Init == outerX = 0

Next == incStep \/ (outerX >= 3 /\ outerX' = outerX)

Spec == Init /\ [][Next]_vars /\ WF_vars(incStep) /\ <> (outerX = 3)
-----------------------------------------------------------------------