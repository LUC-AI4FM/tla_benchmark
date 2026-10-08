------------------------------- MODULE SpanningTreeAlgorithm -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, MaxDistance

VARIABLES Distances, Parents

Init == 
  /\ Distances = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDistance]
  /\ Parents   = [n \in Nodes |-> n]

Next ==
  LET Improvements == {<<n, m>> \in (Nodes \ {Root}) \X (Nodes) :
                         m \in Nodes
                         /\ Distances[m] + 1 < Distances[n]
                         /\ Distances[m] + 1 < MaxDistance
                         /\ Distances[m] + 1 > Distances[n] - 1}
  IN \/ Improvements = {}
     \/ \E <<n, m>> \in Improvements :
          /\ Distances' = [Distances EXCEPT ![n] = Distances[m] + 1]
          /\ Parents'   = [Parents EXCEPT ![n] = m]

Spec ==
  Init /\ [][Next]_<<Distances, Parents>>

Quiescent ==
  \A n \in Nodes \ {Root} :
    \A m \in Nodes :
      NOT (m \in Nodes
           /\ Distances[m] + 1 < Distances[n]
           /\ Distances[m] + 1 < MaxDistance
           /\ Distances[m] + 1 > Distances[n] - 1)

ValidSpanningTree ==
  Quiescent
  /\ \A n \in Nodes :
      (n = Root \/ Parents[n] \in Nodes)
  /\ WF_Parents(Parents, Root)

WF_Parents(p, r) ==
  LET Reachable == {r} \U {n \in Nodes : p[n] \in Reachable}
  IN  (\A n \in Nodes :
         (p[n] = n \/ p[n] \in Reachable))
      /\ (\A n \in Reachable :
          Distances[n] = Distances[p[n]] + 1)

UnreachableNodes ==
  Quiescent
  /\ \A n \in Nodes \ {Root} :
     IF Parents[n] = n THEN Distances[n] = MaxDistance ELSE TRUE

SafetyInvariant ==
  ValidSpanningTree \/ UnreachableNodes

LivenessProperty ==
  <>[](Quiescent)

Fairness ==
  WF_<<Distances, Parents>>(Next)

THEOREM Spec => []SafetyInvariant /\ LivenessProperty
=============================================================================