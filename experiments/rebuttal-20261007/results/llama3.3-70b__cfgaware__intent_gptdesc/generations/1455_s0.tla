---------------------------- MODULE SubsetRelation --------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS SetOfInts, RangeSet, FiniteSet, NatSet, AllIntSet
VARIABLES currentSets, subsetRelations, nonSubsetRelations, globalConsistency

Init ==
  /\ currentSets = {}
  /\ subsetRelations = {}
  /\ nonSubsetRelations = {}
  /\ globalConsistency = TRUE

TypeInvariant ==
  /\ currentSets \in [SetOfInts]
  /\ subsetRelations \in [currentSets -> currentSets]
  /\ nonSubsetRelations \in [currentSets -> currentSets]
  /\ globalConsistency \in BOOLEAN

AddSet(set) ==
  /\ set \in SetOfInts
  /\ currentSets' = currentSets \cup {set}
  /\ subsetRelations' = subsetRelations
  /\ nonSubsetRelations' = nonSubsetRelations
  /\ globalConsistency' = globalConsistency

AssertSubset(set1, set2) ==
  /\ set1 \in currentSets
  /\ set2 \in currentSets
  /\ set1 \subseteq set2
  /\ subsetRelations' = [subsetRelations EXCEPT ![set1] = set2]
  /\ nonSubsetRelations' = nonSubsetRelations
  /\ globalConsistency' = globalConsistency

AssertNonSubset(set1, set2) ==
  /\ set1 \in currentSets
  /\ set2 \in currentSets
  /\ ~(set1 \subseteq set2)
  /\ subsetRelations' = subsetRelations
  /\ nonSubsetRelations' = [nonSubsetRelations EXCEPT ![set1] = set2]
  /\ globalConsistency' = globalConsistency

CheckConsistency ==
  /\ globalConsistency' = globalConsistency
  /\ \A set1 \in currentSets, set2 \in currentSets :
      (set1 \subseteq set2) <=> (set2 \in subsetRelations[set1])
  /\ \A set1 \in currentSets, set2 \in currentSets :
      ~(set1 \subseteq set2) <=> (set2 \in nonSubsetRelations[set1])

Next ==
  \/ \E set \in SetOfInts : AddSet(set)
  \/ \E set1 \in currentSets, set2 \in currentSets : AssertSubset(set1, set2)
  \/ \E set1 \in currentSets, set2 \in currentSets : AssertNonSubset(set1, set2)
  \/ CheckConsistency

Spec ==
  Init /\ [][Next]_<<currentSets, subsetRelations, nonSubsetRelations, globalConsistency>>

THEOREM Spec => []globalConsistency
=============================================================================