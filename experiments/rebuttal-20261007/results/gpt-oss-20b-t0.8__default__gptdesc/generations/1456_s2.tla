------------------------------ MODULE TinyState ------------------------------
EXTENDS SETS

VARIABLES x, y, prev

Init ==
  /\ y \subseteq {1,2,3}
  /\ x \subseteq y
  /\ prev = {}

Next ==
  /\ ANY newX \in SUBSET y :
        /\ x' = newX
        /\ y' = y
        /\ prev' = x

Spec == Init /\ [][Next]_<<x,y,prev>>

FullSet == x = {1,2,3}

GainThree == 3 ∈ x /\ 3 \notin prev

====================================================================