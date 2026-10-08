```
MODULE SubsetRelationModel
EXTENDS Integers, FiniteSets

CONSTANTS IntRange, FiniteSet, SubsetRelations

VARIABLES currentSubsetRelations, globalConsistency

Init ==
  /\ currentSubsetRelations = {}
  /\ globalConsistency = TRUE

Next ==
  /\ IF globalConsistency THEN
    /\ currentSubsetRelations' = currentSubsetRelations
      \cup {<<s1, s2>> : s1 \subseteq s2 /\ s1 \in FiniteSet /\ s2 \in FiniteSet}
      \cup {<<r1, r2>> : r1 \subseteq r2 /\ r1 \in IntRange /\ r2 \in IntRange}
    /\ globalConsistency' = globalConsistency
  ELSE
    /\ currentSubsetRelations' = currentSubsetRelations
    /\ globalConsistency' = globalConsistency

Spec ==
  /\ Init
  /\ [][Next]_currentSubsetRelations, globalConsistency
  /\ WF_vars(Next, currentSubsetRelations, globalConsistency)

Invariant1 == 
  /\ globalConsistency \in BOOLEAN
  /\ globalConsistency = TRUE

Invariant2 == 
  /\ \A s1, s2 \in FiniteSet : (s1 \subseteq s2) => <<s1, s2>> \in currentSubsetRelations
  /\ \A r1, r2 \in IntRange : (r1 \subseteq r2) => <<r1, r2>> \in currentSubsetRelations

Invariant3 == 
  /\ {} \subseteq \A s \in FiniteSet
  /\ \A n, m \in Nat : {1..n} \subseteq {1..m} <=> n <= m
  /\ \A i \in Int : {i} \notin {}

Theorem ==
  Spec => []Invariant1 /\ []Invariant2 /\ []Invariant3

Fairness == 
  /\ WF_vars(Next, currentSubsetRelations, globalConsistency)
```
Note: The `WF_vars` operator is used to specify weak fairness conditions for the variables. This ensures that if the system can make a step (i.e., execute `Next`), it will eventually do so.