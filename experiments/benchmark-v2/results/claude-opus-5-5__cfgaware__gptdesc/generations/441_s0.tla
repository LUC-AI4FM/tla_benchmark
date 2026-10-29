---------------------------- MODULE EnabledSpec ----------------------------
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

Init == x = 0 /\ y = 0

Next == x' = 1 - x /\ y' = y

F == ENABLED (x' = 1 - x /\ y' = y)

G == ENABLED (x' = x /\ y' = y + 1)

SafeSpec == Init /\ [][Next]_<<x, y>>

LiveSpec == SafeSpec /\ WF_<<x, y>>(Next)
=============================================================================