---- MODULE CounterSystem ----
EXTENDS Naturals

VARIABLE outerX

Init == outerX = 0

IncEnabled == outerX < 3

IncStep == /\ IncEnabled
          /\ outerX' = outerX + 1

Stutter == /\ outerX >= 3
           /\ outerX' = outerX

Next == IF outerX < 3 THEN IncStep ELSE Stutter

Spec == Init /\ [] Next /\ WF/IncStep /\ <> (outerX = 3) /\ [](outerX <= 3)

=============================================================================