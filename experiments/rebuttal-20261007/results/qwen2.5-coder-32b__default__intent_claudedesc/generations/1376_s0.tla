------------------------------- MODULE GrowingSet -------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS DataUniverse

VARIABLES currentSet

Init == currentSet = {}

Next ==
  /\ currentSet \in SUBSET DataUniverse
  /\ \/ \E x \in DataUniverse \ currentSet : currentSet' = currentSet \cup {x}
     \/ currentSet' = currentSet

Spec == Init /\ [][Next]_<<currentSet>>

===============================================================================