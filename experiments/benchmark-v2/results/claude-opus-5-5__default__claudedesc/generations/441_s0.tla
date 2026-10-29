---- MODULE EnabledTest ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

Init == x = 0 /\ y = 0

Next == x' = 1 - x /\ y' = y

F == ENABLED (x' = 0 /\ y' = 1)

G == ENABLED ((x # y) /\ x' = 0 /\ y' = 1)

SafeSpec == Init /\ [][Next]_<<x, y>>

LiveSpec == SafeSpec /\ WF_<<x, y>>(Next)

====