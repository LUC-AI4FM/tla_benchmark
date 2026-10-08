MODULE SubsetSpec
EXTENDS SETS

VARIABLE b

Init == b = TRUE

Next ==
  /\ b' = ({1,2} \subseteq {1,2,3})
  /\ ~({4} \subseteq {1,2,3})
  /\ (1..5 \subseteq 1..10)
  /\ ~(6..10 \subseteq 1..5)
  /\ (Nat \subseteq Int)
  /\ ~(Int \subseteq Nat)

SafetyInvariant == b \in BOOLEAN /\ b = TRUE

Spec == Init /\ [][Next]_<<b>> /\ SafetyInvariant