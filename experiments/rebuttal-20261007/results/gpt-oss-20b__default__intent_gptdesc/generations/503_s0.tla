MODULE Consensus

EXTENDS Naturals, TLC

CONSTANTS Values, None

VARIABLES chosenVal, proposedSet

Init ==
  /\ chosenVal = None
  /\ proposedSet = {}

Propose(v) ==
  /\ v ∈ Values
  /\ v ∉ proposedSet
  /\ chosenVal = None
  /\ proposedSet' = proposedSet ∪ {v}
  /\ chosenVal' = chosenVal

Learn(v) ==
  /\ v ∈ Values
  /\ v ∈ proposedSet
  /\ chosenVal = None
  /\ chosenVal' = v
  /\ proposedSet' = proposedSet

Next == ∃ v ∈ Values : Propose(v) \/ Learn(v)

SafetyInv == (chosenVal = None \/ chosenVal ∈ Values)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Liveness == <> (chosenVal ∈ Values)