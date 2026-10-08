----------------------------- MODULE SpanningTree -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    Nodes,    \* finite, nonempty set of node identifiers
    Root,     \* designated root in Nodes
    MaxDist,  \* an upper bound on distances, at least Cardinality(Nodes)
    Adj       \* undirected adjacency relation: a subset of Nodes \X Nodes

ASSUME
  /\ Nodes /= {}
  /\ Root \in Nodes
  /\ MaxDist \in Nat
  /\ MaxDist >= Cardinality(Nodes)
  /\ Adj \subseteq Nodes \X Nodes
  /\ \A u \in Nodes : <<u,u>> \notin Adj
  /\ \A u \in Nodes : \A v \in Nodes : (<<u,v>> \in Adj) <=> (<<v,u>> \in Adj)

VARIABLES dist, parent

Vars == << dist, parent >>

Edge(u,v) == <<u,v>> \in Adj

Init ==
  /\ dist \in [Nodes -> 0..MaxDist]
  /\ parent \in [Nodes -> Nodes]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDist]
  /\ parent = [n \in Nodes |-> n]

\* A node u can improve if it has a neighbor v whose distance is at least 1 less than u's,
\* i.e., dist[v] + 1 < dist[u]. (This implies there exists an integer new distance strictly
\* less than dist[u] and at least dist[v]+1.)
CanImprove(u) ==
  \E v \in Nodes : Edge(u,v) /\ dist[v] + 1 < dist[u]

\* Improvement step: u adopts neighbor v as parent and picks a new distance nd
\* with dist[v] + 1 <= nd < dist[u], strictly improving its distance.
Improve(u,v,nd) ==
  /\ u \in Nodes
  /\ v \in Nodes
  /\ Edge(u,v)
  /\ nd \in 0..MaxDist
  /\ dist[v] + 1 <= nd
  /\ nd < dist[u]
  /\ dist' = [dist EXCEPT ![u] = nd]
  /\ parent' = [parent EXCEPT ![u] = v]

Next ==
  \E u \in Nodes : \E v \in Nodes : \E nd \in 0..MaxDist : Improve(u,v,nd)

Spec == Init /\ [][Next]_Vars

\* Basic typing and structure invariants (safety).
TypeOK ==
  /\ dist \in [Nodes -> 0..MaxDist]
  /\ parent \in [Nodes -> Nodes]

ParentIsSelfOrNeighbor ==
  \A u \in Nodes : parent[u] = u \/ Edge(u, parent[u])

RootFixed ==
  /\ dist[Root] = 0
  /\ parent[Root] = Root

\* Quiescent when no node can improve its distance.
Quiescent == \A u \in Nodes : ~CanImprove(u)

\* Reachability from Root in the (fixed) undirected graph Adj, bounded by MaxDist.
RECURSIVE ReachableUpTo(_)
ReachableUpTo(k) ==
  IF k = 0 THEN {Root}
  ELSE
    LET Prev == ReachableUpTo(k-1) IN
      Prev \cup { n \in Nodes : \E m \in Prev : Edge(n,m) }

Reachable == ReachableUpTo(MaxDist)

\* When quiescent, reachable nodes form a valid spanning tree
\* (dist equals parent's dist + 1 along edges), and unreachable
\* nodes remain at MaxDist with no reachable neighbors.
ValidResult ==
  /\ RootFixed
  /\ \A u \in (Reachable \ {Root}) :
       /\ Edge(u, parent[u])
       /\ dist[u] = dist[parent[u]] + 1
  /\ \A u \in (Nodes \ Reachable) :
       /\ dist[u] = MaxDist
       /\ parent[u] = u
       /\ \A v \in Nodes : Edge(u,v) => v \notin Reachable

Safety ==
  /\ TypeOK
  /\ ParentIsSelfOrNeighbor
  /\ (Quiescent => ValidResult)

\* Liveness: the algorithm eventually becomes quiescent forever.
Liveness == <>[] Quiescent

=============================================================================