------------------------------ MODULE SpanningTree ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS
    NODES,   \* Fixed set of nodes
    EDGES,   \* Set of undirected edges, each edge is a two-element set {u, v} of distinct nodes in NODES
    Root,    \* Distinguished root node
    UB       \* Upper bound on the number of nodes; used as "infinity" for distances

ASSUME
    /\ Root \in NODES
    /\ UB \in Nat
    /\ \A e \in EDGES:
         \E a \in NODES:
           \E b \in NODES:
             /\ a /= b
             /\ e = {a, b}

VARIABLES
    dist,    \* [NODES -> Nat], current distance estimates
    parent   \* [NODES -> NODES], current parent pointers

vars == << dist, parent >>

IsNeighbor(u, v) == {u, v} \in EDGES

Neighbors(n) == { m \in NODES : IsNeighbor(m, n) }

Init ==
    /\ dist \in [NODES -> Nat]
    /\ parent \in [NODES -> NODES]
    /\ dist[Root] = 0
    /\ parent[Root] = Root
    /\ \A v \in NODES \ {Root}:
         /\ dist[v] = UB
         /\ parent[v] = v

\* Single-node improvement: choose a neighbor with strictly better distance and lower v's distance,
\* to some value at least the neighbor's distance + 1 and strictly less than v's current distance.
ImproveNode(v) ==
    \E u \in Neighbors(v):
      /\ dist[v] > dist[u] + 1
      /\ \E newd \in Nat:
           /\ dist[u] + 1 <= newd
           /\ newd < dist[v]
           /\ dist' = [dist EXCEPT ![v] = newd]
           /\ parent' = [parent EXCEPT ![v] = u]

Improve ==
    \E v \in NODES: ImproveNode(v)

NoOp ==
    UNCHANGED vars

Next ==
    Improve \/ NoOp

\* Type and basic invariants that should hold in all states
TypeOK ==
    /\ dist \in [NODES -> Nat]
    /\ parent \in [NODES -> NODES]
    /\ \A v \in NODES: dist[v] <= UB
    /\ dist[Root] = 0
    /\ parent[Root] = Root

\* Termination condition: no node can further improve using any neighbor
Terminated ==
    \A v \in NODES:
      \A u \in Neighbors(v):
        dist[v] <= dist[u] + 1

\* Graph reachability from Root via undirected edges
IsWalk(s) ==
    /\ Len(s) >= 1
    /\ \A i \in 1..(Len(s) - 1): IsNeighbor(s[i], s[i+1])

Reachable(n) ==
    \E s \in Seq(NODES):
      /\ IsWalk(s)
      /\ s[1] = Root
      /\ s[Len(s)] = n

\* Safety at termination: parent defines a rooted spanning tree of the Root-reachable nodes,
\* and unreachable nodes remain at distance UB with self-parent and no neighbor with smaller distance.
TreeOK ==
    /\ dist[Root] = 0
    /\ parent[Root] = Root
    /\ \A n \in NODES:
         IF n = Root THEN TRUE
         ELSE IF ~Reachable(n) THEN
              /\ dist[n] = UB
              /\ parent[n] = n
              /\ \A u \in Neighbors(n): dist[u] >= dist[n]
         ELSE
              /\ parent[n] \in Neighbors(n)
              /\ dist[n] = dist[parent[n]] + 1

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Improve)

\* Safety and liveness properties to be checked
AlwaysTypeOK ==
    []TypeOK

Termination ==
    <>Terminated

TreeSafety ==
    [](Terminated => TreeOK)

=============================================================================