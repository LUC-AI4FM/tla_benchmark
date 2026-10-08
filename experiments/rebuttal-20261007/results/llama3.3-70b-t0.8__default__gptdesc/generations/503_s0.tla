```
MODULE SingleValueConsensus
EXTENDS Integers
CONSTANTS Values
VARIABLES chosen

Init == (chosen = {})

Next == (chosen = {}) /\ (chosen' = {v} /\ v \in Values) \/ (chosen /= {} /\ chosen' = chosen)

Spec == Init /\ [][Next]_chosen

AtMostOneValueChosen == [](chosen \subseteq {x \in Values : x = v} /\ ~<<v>> \in [Values])

THEOREM Spec => []AtMostOneValueChosen

LivenessSpec == Spec /\ WF_vars(Next)

THEOREM LivenessSpec => <>~(chosen = {})
```