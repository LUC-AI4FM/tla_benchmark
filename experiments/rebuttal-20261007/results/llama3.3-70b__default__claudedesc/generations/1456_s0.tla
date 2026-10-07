```
MODULE SubsetConstraints
EXTENDS Integers, FiniteSets

CONSTANTS 

VARIABLES x, y

Init == 
  (x \subseteq {1, 2}) /\ (y = {1, 2, 3})

Next == 
  (y' = y) /\ (x' \subseteq y')

TypeOK == x \subseteq {1, 2, 3}
Inv == (<<x' \subseteq {1}>>_x \in Next) /\ (y = {1, 2, 3})

FullSet == x = {1, 2, 3}
GainThree == (3 \notin x) /\ (3 \in x')

Spec == Init /\ [][Next]_<<x, y>>
WF_Spec == Spec /\ WF_<<x, y>>(Next)

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => <><FullSet>_x
THEOREM Spec => <<GainThree>>_x

PossibleCounts == 
  (FullSet._POSSIBLE = 8) /\ (GainThree._TRANSITIONS = 16)
```