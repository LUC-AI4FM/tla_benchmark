```
MODULE M
VARIABLES active, color, tpos, tcolor

Nodes == 0..2
TokenColors == {"white", "black"}

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> TokenColors]
  /\ tpos \in Nodes
  /\ tcolor = "black"

Next ==
  /\ active' \in [{23, 42, 56} -> BOOLEAN]
  /\ color' \in [Nodes -> TokenColors]
  /\ tpos' \in Nodes
  /\ tcolor' = "black"

Spec == Init /\ [][Next]_vars

THEOREM Spec => [](tcolor = "black")
```
Note: The `THEOREM` statement is not strictly necessary for the model-checking configuration to bind, but it's included here as a sanity check to ensure that the specification indeed implies the token color remains fixed at `"black"`.