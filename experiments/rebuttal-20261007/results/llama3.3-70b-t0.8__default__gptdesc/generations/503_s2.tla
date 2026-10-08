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

AtMostOneValueChosen == [](chosen \subseteq {x} \/ chosen = {})

Theorem == Spec => []AtMostOneValueChosen

StrongerSpec == Spec /\ WF_vars(Next)

THEOREM StrongerSpec => <>~(chosen = {})
```