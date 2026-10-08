```
MODULE CigaretteSmokers
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients
VARIABLES offer, smoking, finished

Init ==
  /\ offer = {}
  /\ smoking = {}
  /\ finished = {}

Next ==
  \/ \E i \in Ingredients :
      /\ offer = [j \in Ingredients |-> IF j = i THEN {} ELSE {j}]
      /\ smoking' = {}
      /\ finished' = {}
  \/ \E s \in Ingredients :
      /\ smoking = {s}
      /\ offer' = {}
      /\ finished' = {s}
  \/ \E s \in Ingredients :
      /\ smoking = {}
      /\ offer' = [j \in Ingredients |-> IF j = s THEN {} ELSE {j}]
      /\ finished' = {}

Spec ==
  Init /\ [][Next]_<<offer, smoking, finished>>

TypeInvariant ==
  /\ offer \in SUBSET Ingredients
  /\ smoking \subseteq Ingredients
  /\ finished \subseteq Ingredients

DomainInvariant ==
  /\ \E i \in Ingredients : i \notin offer => offer = [j \in Ingredients |-> IF j = i THEN {} ELSE {j}]
  /\ Card(smoking) <= 1

SafetyInvariant ==
  Card(smoking) <= 1

LivenessProperty ==
  WF_<<offer, smoking, finished>>(\E s \in Ingredients : 
    /\ offer = [j \in Ingredients |-> IF j = s THEN {} ELSE {j}]
    /\ smoking' = {s}
    /\ finished' = {}
  )

ProgressOfOffers ==
  SF_<<offer, smoking, finished>>(offer /= {})

THEOREM Spec => []TypeInvariant
THEOREM Spec => []DomainInvariant
THEOREM Spec => []SafetyInvariant
THEOREM Spec => LivenessProperty
THEOREM Spec => ProgressOfOffers
```