```
MODULE SingleValueConsensus
EXTENDS Integers, FiniteSets

CONSTANTS Values

VARIABLES chosen

Init == (chosen = {})

Next == (chosen = {}) /\ (chosen' = {v} \/ chosen' = chosen)
            /\ (v \in Values)

Spec == Init /\ [][Next]_chosen

AtMostOneTheorem == []((chosen = {}) \/ (Cardinality(chosen) = 1))

THEOREM Spec => []AtMostOneTheorem

Fairness == WF_vars(Next, chosen)

LivenessSpec == Spec /\ Fairness
```