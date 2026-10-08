------------------------------ MODULE DijkstraScholtenStub ------------------------------
EXTENDS Naturals

CONSTANTS Nodes
CONSTANTS Colors

VARIABLES nodeActivity, nodeColor, tokenPos, tokenColor

(* -- Type Invariant ----------------------------------------------------------- *)
TypeInv == 
  /\ nodeActivity \in [Nodes -> BOOLEAN]
  /\ nodeColor   \in [Nodes -> Colors]
  /\ tokenPos    \in Nodes
  /\ tokenColor  \in Colors
  /\ tokenColor = "black"

(* -- Initial State ------------------------------------------------------------ *)
Init ==
  /\ nodeActivity \in [Nodes -> BOOLEAN]
  /\ nodeColor   \in [Nodes -> Colors]
  /\ tokenPos    \in Nodes
  /\ tokenColor  = "black"

(* -- Next-State Relation (unconstrained transitions) -------------------------- *)
Next ==
  \E newNodeAct \in [Nodes -> BOOLEAN] :
    \E newNodeCol \in [Nodes -> Colors] :
      \E newTokenPos \in Nodes :
        /\ nodeActivity' = newNodeAct
        /\ nodeColor'   = newNodeCol
        /\ tokenPos'    = newTokenPos
        /\ tokenColor'  = "black"

(* -- Specification ------------------------------------------------------------ *)
Spec == Init /\ [][Next]_<<nodeActivity, nodeColor, tokenPos, tokenColor>>

=============================================================================