MODULE SingleValueConsensus

EXTENDS Naturals, TLC

CONSTANTS Values

VARIABLE chosen

Init == 
  chosen = {}

Next ==
  /\ chosen = {}
  /\ ∃ v ∈ Values : chosen' = {v}

Spec == 
  Init
  /\ [][Next]_chosen
  /\ WF_vars(Next)

SafetyInvariant == 
  [] (chosen = {} \/ #chosen = 1)

THEOREM ChosenAtMostOnce == SafetyInvariant

LEMMA EventuallyChosen == <> (chosen ≠ {})