```
MODULE MultiInstanceConsensus
EXTENDS Integers, FiniteSets

CONSTANTS ValueDomain, Slots
VARIABLES proposedValues, chosenValues

Init ==
  /\ proposedValues = {}
  /\ chosenValues = [s \in Slots |-> {}]

Next ==
  \/ \E v \in ValueDomain :
      /\ proposedValues' = proposedValues \cup {v}
      /\ chosenValues' = chosenValues
  \/ \E s \in Slots, v \in proposedValues :
      /\ proposedValues' = proposedValues
      /\ chosenValues' = [chosenValues EXCEPT ![s] = {v}]

Spec ==
  Init /\ [][Next]_<<proposedValues, chosenValues>>

ProposedValueInvariant ==
  \A s \in Slots : chosenValues[s] \subseteq proposedValues

UniqueChosenValueInvariant ==
  \A s \in Slots : Cardinality(chosenValues[s]) <= 1

PersistentChosenValueInvariant ==
  \A s \in Slots : chosenValues[s] = {} \/ chosenValues'[s] = chosenValues[s]

TypeInvariant ==
  /\ proposedValues \subseteq ValueDomain
  /\ \A s \in Slots : chosenValues[s] \subseteq ValueDomain

SafetyProperty ==
  ProposedValueInvariant /\ UniqueChosenValueInvariant /\ PersistentChosenValueInvariant

FairnessCondition ==
  WF_<<proposedValues, chosenValues>>(Next)

LivenessProperty ==
  \A s \in Slots : <>chosenValues[s] /= {}

THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyProperty
THEOREM Spec /\ FairnessCondition => LivenessProperty
```