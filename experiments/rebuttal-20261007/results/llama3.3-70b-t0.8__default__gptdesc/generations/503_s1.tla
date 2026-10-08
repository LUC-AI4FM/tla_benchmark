```
MODULE SingleValueConsensus
EXTENDS Integers, TLC
CONSTANTS Values
VARIABLES chosen

Init == (chosen = {})

Next == (chosen = {} /\ chosen' = {v} /\ v \in Values) 
       \/ (chosen /= {} /\ UNCHANGED chosen)

Spec == Init /\ [][Next]_chosen

AtMostOneValueChosen == [](chosen \subseteq {x \in Values : x = y} \/ chosen = {})
Theorem == Spec => []AtMostOneValueChosen

WF_Next == <>[]<>(chosen /= {} /\ UNCHANGED chosen)
LiveSpec == Spec /\ WF_<<Next>>_chosen
```