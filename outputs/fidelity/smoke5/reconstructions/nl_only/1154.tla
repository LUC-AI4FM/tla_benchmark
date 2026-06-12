---- MODULE MC ----
EXTENDS Grid5k, stats

CONSTANTS PlaceholderConstant

VARIABLES placeholderVariable

vars == <<placeholderVariable>>

Init == TRUE

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

====