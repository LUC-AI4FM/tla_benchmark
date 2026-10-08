------------------------------ MODULE Counter ------------------------------
EXTENDS Naturals

VARIABLES c

Init == c = 0

Inc == c < 3 /\ c' = c + 1

Stutter == c >= 3 /\ c' = c

Next == Inc \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF(Inc)

=============================================================================