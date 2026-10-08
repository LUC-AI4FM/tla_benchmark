---- MODULE RootedSpanningTree ----
EXTENDS Naturals

CONSTANTS Nodes, Root, Adj, MaxCardinality

(* Assume adjacency is undirected and defined over Nodes *)
ASSUME \A n,m \in Nodes : (Adj[n,m] => Adj[m,n])

VARIABLES mom, dist

Variables == <<mom, dist>>

Init ==
  /\ \A v \in Nodes : mom[v] = v
  /\ dist[Root] = 0
  /\ \A v \in Nodes \ {Root} : dist[v] = MaxCardinality
  /\ \A v,w \in Nodes : Adj[v,w] => w \in Nodes

TypeInvariant ==
  /\ \A v \in Nodes : mom[v] \in Nodes
  /\ \A v \in Nodes : 0 <= dist[v] /\ dist[v] <= MaxCardinality

(* Postcondition: correct rooted spanning tree *)
PostCond ==
  /\ dist[Root] = 0
  /\ \A u \in Nodes :
        IF u = Root THEN dist[u] = 0
        ELSE (Adj[u, mom[u]] /\ dist[u] > 0 /\ dist[u] = 1 + dist[mom[u]])

TerminationCondition ==
  \A n \in Nodes : ~\E m \in Nodes : Adj[n,m] /\ dist[m] < dist[n]

SafetyInvariant ==
  TerminationCondition => PostCond

Next ==
  LET
    candidates == \{ <<n, m>> |
        n \in Nodes /\ m \in Nodes /\ Adj[n,m] /\
        dist[m] + 2 <= dist[n]
      \}
  IN
    \E pair \in candidates :
      LET n          == pair[1],
          m          == pair[2],
          newDist    == CHOOSE d \in Nat : (dist[m] + 1) <= d /\ d < dist[n]
      IN
        /\ mom' = [v |-> IF v = n THEN m ELSE mom[v]]
        /\ dist' = [v |-> IF v = n THEN newDist ELSE dist[v]]
        /\ TypeInvariant

Spec ==
  Init /\ []TypeInvariant /\ [][Next]_Variables /\ WF_∃ Next

TerminationLiveness == ◇ TerminationCondition
RootParentEventually ==
  \A v \in Nodes \ {Root} : ◇ (mom[v] = Root)

====