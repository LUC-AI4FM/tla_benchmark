------------------------------ MODULE SpanningTree ------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, MaxDist

ASSUME
  /\ IsFiniteSet(Nodes)
  /\ Root \in Nodes
  /\ MaxDist \in Nat
  /\ MaxDist >= Cardinality(Nodes)

VARIABLES E, dist, parent

vars == << E, dist, parent >>

AllUndirEdges == { {u, v} : u \in Nodes, v \in Nodes, u # v }

IsEdge(u, v) == u # v /\ {u, v} \in E

Neigh(v) == { u \in Nodes : IsEdge(u, v) }

Init ==
  /\ E \in SUBSET AllUndirEdges
  /\ dist \in [Nodes -> 0..MaxDist]
  /\ parent \in [Nodes -> Nodes]
  /\ dist[Root] = 0
  /\ parent[Root] = Root
  /\ \A v \in Nodes \ {Root}:
        /\ dist[v] = MaxDist
        /\ parent[v] = v

Improvement(v, u, d) ==
  /\ v \in Nodes \ {Root}
  /\ u \in Neigh(v)
  /\ dist[u] + 1 < dist[v]
  /\ d \in 0..MaxDist
  /\ dist[u] + 1 <= d
  /\ d < dist[v]

Next ==
  \E v \in Nodes \ {Root}:
    \E u \in Neigh(v):
      \E d \in 0..MaxDist:
        /\ Improvement(v, u, d)
        /\ E' = E
        /\ dist' = [dist EXCEPT ![v] = d]
        /\ parent' = [parent EXCEPT ![v] = u]

Quiescent ==
  \A v \in Nodes \ {Root}:
    \A u \in Neigh(v): dist[u] + 1 >= dist[v]

REACHABLE(v) ==
  v = Root \/
  \E s \in Seq(Nodes):
    /\ Len(s) >= 1
    /\ s[1] = Root
    /\ s[Len(s)] = v
    /\ \A i \in 1..(Len(s)-1): IsEdge(s[i], s[i+1])

ValidFinal ==
  /\ dist[Root] = 0
  /\ parent[Root] = Root
  /\ \A v \in Nodes \ {Root}:
       IF REACHABLE(v)
       THEN /\ parent[v] \in Neigh(v)
            /\ dist[v] = dist[parent[v]] + 1
       ELSE /\ dist[v] = MaxDist
            /\ \A u \in Neigh(v): ~REACHABLE(u)

TypeOK ==
  /\ E \subseteq AllUndirEdges
  /\ dist \in [Nodes -> 0..MaxDist]
  /\ parent \in [Nodes -> Nodes]

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

Safety == [] (Quiescent => ValidFinal)

Liveness == <>Quiescent

=============================================================================