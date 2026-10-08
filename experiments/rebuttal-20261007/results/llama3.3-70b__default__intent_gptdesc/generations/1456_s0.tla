```
MODULE MutableSubset
EXTENDS Integers, FiniteSets

CONSTANTS Universe

VARIABLES subset

Init ==
  /\ subset \subseteq Universe
  /\ subset \subset Universe
  /\ Universe = {1, 2, 3}

Next ==
  /\ Universe' = Universe
  /\ subset' \subseteq Universe

Spec ==
  Init /\ [][Next]_<<Universe, subset>>

THEOREM Spec => []subset \subseteq Universe
THEOREM Spec => <>[](subset = Universe)

THEOREM Spec => <>(subset' = Universe)_
THEOREM Spec => [](Universe' = Universe)

FullSetReached == subset = Universe

ElementGained(e) == e \notin subset /\ e \in subset'

THEOREM Spec => WF_(subset, ElementGained(3))
```
Note: The `WF_` operator is used to express weak fairness. It ensures that if a transition that adds an element (e.g., 3) is continuously enabled, it will eventually occur.