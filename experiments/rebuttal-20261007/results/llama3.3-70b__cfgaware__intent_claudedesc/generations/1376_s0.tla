---------------------------- MODULE GrowingSet ----------------------------
EXTENDS Integers

CONSTANT DataValues
VARIABLE growingSet

Init == (growingSet = {})

AddElement ==
  /\ growingSet' = growingSet \cup {x}
  /\ x \in DataValues

Next == \E x \in DataValues : AddElement

Spec == Init /\ [][Next]_growingSet

THEOREM Spec => []Init
=============================================================================