MODULE DijkstraScholtenStub
EXTENDS SETS

CONSTANTS Nodes, Colors

VARIABLES nodeAct, nodeCol, tokenPos, tokenCol

TypeInv ==
  /\ nodeAct \in [Nodes -> BOOLEAN]
  /\ nodeCol \in [Nodes -> Colors]
  /\ tokenPos \in Nodes
  /\ tokenCol \in Colors
  /\ tokenCol = "black"

Init ==
  /\ nodeAct \in [Nodes -> BOOLEAN]
  /\ nodeCol \in [Nodes -> Colors]
  /\ tokenPos \in Nodes
  /\ tokenCol = "black"

Next ==
  \E nodeAct', nodeCol', tokenPos', tokenCol' :
    /\ nodeAct' \in [Nodes -> BOOLEAN]
    /\ nodeCol' \in [Nodes -> Colors]
    /\ tokenPos' \in Nodes
    /\ tokenCol' = tokenCol

Spec == Init /\ [][Next]_<<nodeAct,nodeCol,tokenPos,tokenCol>> /\ TypeInv

Safety == TypeInv

END MODULE