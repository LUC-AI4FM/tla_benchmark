```
MODULE SingleValueConsensus
EXTENDS Integers

CONSTANTS Candidates
VARIABLES Chosen

Init == Chosen = {}

Next == 
  \/ (Chosen = {} /\ \E v \in Candidates : Chosen' = {v})
  \/ (Chosen /= {} /\ Chosen' = Chosen)

Spec == Init /\ [][Next]_Chosen

SafetyInvariant == 
  Chosen \subseteq Candidates
  /\ *Chosen <= 1

FairnessCondition == WF_v(v \in Candidates)(Chosen = {} /\ v \in Candidates -> Chosen' = {v})

LivenessProperty == <>~(Chosen = {})
```
Note: The `*` operator is used to denote the cardinality of a set, i.e., `*S` represents the number of elements in set `S`. 

Also note that this model does not explicitly encode weak fairness. To do so, we would need to introduce additional variables and actions to track when a choice is possible and ensure it eventually happens.

Here's an updated version with explicit weak fairness:
```
MODULE SingleValueConsensusFair
EXTENDS Integers

CONSTANTS Candidates
VARIABLES Chosen, Enabled

Init == Chosen = {} /\ Enabled = FALSE

Next == 
  \/ (Chosen = {} /\ \E v \in Candidates : Chosen' = {v} /\ Enabled' = TRUE)
  \/ (Chosen /= {} /\ Chosen' = Chosen /\ Enabled' = Enabled)
  \/ (Enabled = FALSE /\ Enabled' = TRUE)

Spec == Init /\ [][Next]_(Chosen, Enabled)

SafetyInvariant == 
  Chosen \subseteq Candidates
  /\ *Chosen <= 1

FairnessCondition == WF_v(v \in Candidates)(Enabled -> <>~(Chosen = {v}))

LivenessProperty == <>~(Chosen /= {})
```