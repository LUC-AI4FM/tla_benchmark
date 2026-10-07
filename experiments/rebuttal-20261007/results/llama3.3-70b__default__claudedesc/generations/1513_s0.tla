```
MODULE M
EXTENDS Integers, FiniteSets
CONSTANTS Nodes
VARIABLES active, color, tpos, tcolor

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> {"white", "black"}]
  /\ tpos \in Nodes
  /\ tcolor = "black"

Next ==
  /\ active' \in [{23, 42, 56} -> BOOLEAN]
  /\ color' \in [{23, 42, 56} -> {"white", "black"}]
  /\ tpos' \in {23, 42, 56}
  /\ tcolor' = "black"

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
```