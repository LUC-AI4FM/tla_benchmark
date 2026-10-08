---------------------------- MODULE SpanningTree ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Nodes, Edges, Root, MaxDistance
VARIABLE parent, distance

TypeOK == 
  /\ Nodes \subseteq Nat
  /\ Edges \subseteq (SUBSET Nodes)
  /\ Root \in Nodes
  /\ MaxDistance \in Nat

Init ==
  /\ distance = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDistance]
  /\ parent = [n \in Nodes |-> n]

Next ==
  \E n \in Nodes, d \in Nat, p \in Nodes :
    /\ distance[n] > 1 + distance[p]
    /\ {n, p} \in Edges
    /\ d \in (distance[p] + 1)..(distance[n] - 1)
    /\ distance' = [distance EXCEPT ![n] = d]
    /\ parent' = [parent EXCEPT ![n] = p]

Spec == Init /\ [][Next]_<<parent, distance>>

Safety ==
  /\ distance[Root] = 0
  /\ parent[Root] = Root
  /\ \A n \in Nodes :
      \/ distance[n] = MaxDistance
        /\ parent[n] = n
        /\ \A p \in Nodes : {n, p} \in Edges => distance[p] >= distance[n]
      \/ distance[n] = distance[parent[n]] + 1
        /\ {n, parent[n]} \in Edges

Liveness == <>(\A n \in Nodes : 
  \E p \in Nodes : {n, p} \in Edges => distance[n] <= 1 + distance[p])

THEOREM Spec => []Safety
THEOREM Spec => Liveness
=============================================================================