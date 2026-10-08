------------------------------- MODULE SimpleStateMachine -------------------------------
EXTENDS TLC, Integers

CONSTANTS Nodes, Colors
ASSUME NodeSet \subseteq Nat /\ Cardinality(NodeSet) = Nodes
ASSUME ColorSet \subseteq {"red", "blue"} /\ Cardinality(ColorSet) = Colors

VARIABLES nodeActivity, nodeColors, tokenPosition, tokenColor

Init == 
  /\ nodeActivity \in [NodeSet -> BOOLEAN]
  /\ nodeColors \in [NodeSet -> ColorSet]
  /\ tokenPosition \in NodeSet
  /\ tokenColor \in ColorSet

Next ==
  \/ \E n \in NodeSet : 
     (nodeActivity' = [nodeActivity EXCEPT ![n] = ~nodeActivity[n]]
      /\ nodeColors' = nodeColors
      /\ tokenPosition' = tokenPosition
      /\ tokenColor' = tokenColor)
  \/ \E c \in ColorSet :
     (nodeActivity' = nodeActivity
      /\ nodeColors' = [nodeColors EXCEPT ![tokenPosition] = c]
      /\ tokenPosition' = tokenPosition
      /\ tokenColor' = tokenColor)
  \/ \E n \in NodeSet : 
     (nodeActivity' = nodeActivity
      /\ nodeColors' = nodeColors
      /\ tokenPosition' = n
      /\ tokenColor' = tokenColor)

Spec == Init /\ [][Next]_<<nodeActivity, nodeColors, tokenPosition, tokenColor>>
====================================================================