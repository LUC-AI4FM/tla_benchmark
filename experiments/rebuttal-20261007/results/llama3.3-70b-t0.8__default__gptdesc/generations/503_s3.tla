```
MODULE SingleValueConsensus
EXTENDS Integers, TLC

CONSTANTS Values
VARIABLES chosen

Init == (chosen = {})

Next == ( chosen = {} ) \/ ( chosen' = chosen )
          \* change chosen from {} to {v} for some v in Values
       \/ ( EXISTS v \in Values :
              chosen' = {v} 
          )

Spec == Init /\ [][Next]_chosen

AtMostOneValueChosen == []( ~ (EXISTS v1, v2 \in chosen : v1 # v2) )
THEOREM Spec => []AtMostOneValueChosen

FairSpec == Spec /\ WF_vars(Next)

LivenessTheorem == FairSpec => <>(<>(chosen # {}))

THEOREM FairSpec => LivenessTheorem
```