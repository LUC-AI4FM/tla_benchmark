------------------------------- MODULE GrowingSet -------------------------------

CONSTANTS DataUniverse

VARIABLES currentSet

Init == currentSet = {}

Next ==
    /\ \/ \E x \in DataUniverse : currentSet' = currentSet \cup {x}
       \/ currentSet' = currentSet

Spec == Init /\ [][Next]_<<currentSet>>

===============================================================================