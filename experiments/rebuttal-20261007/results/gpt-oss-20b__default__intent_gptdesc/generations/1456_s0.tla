MODULE MutableSubset
EXTENDS FiniteSets, TLC

CONSTANTS UNIVERSE == {1,2,3}

VARIABLES subset, univ

Init ==
  /\ univ = UNIVERSE
  /\ subset \in Subset(univ)
  /\ subset # univ

Next ==
  /\ univ' = univ
  /\ subset' \in Subset(univ)

SafetyInvariant == subset \subseteq univ
UniverseInvariant == univ = UNIVERSE

FullSetReached == subset = univ
ElementGained3 ==
  /\ 3 ∉ subset
  /\ 3 ∈ subset'

Spec == Init /\ [][Next]_<<subset,univ>> /\ SafetyInvariant /\ UniverseInvariant