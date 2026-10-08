------------------------------ MODULE SpanningTree ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Edges, Root, UpperBound

(* Derived constants *)
NodesSet == Nodes
EdgesSet == Edges
RootNode == Root
UBound == UpperBound

(* Helper definitions *)
Neighbor(n) == { m \in Nodes : n # m /\ {n,m} \in Edges }

VARIABLES dist, parent

Init ==
  /\ dist = [n \in Nodes |-> IF n = RootNode THEN 0 ELSE UBound]
  /\ parent = [n \in Nodes |-> IF n = RootNode THEN RootNode ELSE n]

Update(n, m, newDist) ==
  /\ n \in Nodes
  /\ m \in Neighbor(n)
  /\ dist[n] > dist[m] + 1
  /\ newDist > dist[m] + 1
  /\ newDist < dist[n]
  /\ newDist <= UBound
  /\ newDist \in Nat
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ dist'   = [dist EXCEPT ![n] = newDist]

Next ==
  \E n \in Nodes :
    \E m \in Neighbor(n) :
      \E newDist \in Nat :
        Update(n, m, newDist)

(* Safety invariants *)
RootInvariant ==
  /\ dist[RootNode] = 0
  /\ parent[RootNode] = RootNode

UnreachableInvariant ==
  \A n \in Nodes :
    IF dist[n] = UBound THEN
      /\ parent[n] = n
      /\ \A m \in Neighbor(n) : dist[m] >= dist[n]
    ELSE TRUE

ReachableInvariant ==
  \A n \in Nodes :
    IF n # RootNode /\ dist[n] < UBound THEN
      /\ parent[n] \in Neighbor(n)
      /\ dist[n] = dist[parent[n]] + 1
    ELSE TRUE

DistanceBounds ==
  \A n \in Nodes : 0 <= dist[n] /\ dist[n] <= UBound

SafetyInvariant ==
  RootInvariant /\ UnreachableInvariant /\ ReachableInvariant /\ DistanceBounds

(* Termination condition *)
NoImprovement ==
  \A n \in Nodes :
    \A m \in Neighbor(n) :
      dist[n] <= dist[m] + 1

Termination == []<>(NoImprovement)

Spec ==
  Init
  /\ [][Next]_<<dist, parent>>
  /\ []SafetyInvariant
  /\ Termination

=============================================================================