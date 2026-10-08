```
MODULE SingleValueConsensus
EXTENDS Integers, TLC

CONSTANTS Values

VARIABLES chosen

Init == (chosen = {})

Next == 
  IF chosen = {} 
  THEN chosen' = {x} /\ x \in Values
  ELSE chosen' = chosen

Spec == Init /\ [][Next]_chosen

AtMostOneValueChosen == [](Cardinality(chosen) <= 1)
TheoremAtMostOneValueChosen == Spec => []AtMostOneValueChosen

Fairness == WF_vars(Next, chosen)

LivenessSpec == Spec /\ Fairness
```