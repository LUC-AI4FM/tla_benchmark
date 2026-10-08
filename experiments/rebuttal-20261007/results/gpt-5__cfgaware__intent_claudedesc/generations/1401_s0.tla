--------------------------- MODULE Inner ---------------------------
EXTENDS Naturals

VARIABLE x

Init == x = 0

Inc == x < 3 /\ x' = x + 1

Fair == WF_x(Inc)

ISpec == Init /\ [][Inc \/ UNCHANGED x]_x /\ Fair
====================================================================