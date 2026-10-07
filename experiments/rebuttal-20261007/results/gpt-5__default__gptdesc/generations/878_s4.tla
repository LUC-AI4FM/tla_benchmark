---------------------------- MODULE RootedSpanningTree ----------------------------

EXTENDS Naturals

CONSTANTS Nodes, Root, Adj, MaxCardinality

ASSUME
  /\ Root \in Nodes
  /\ Adj \subseteq Nodes \times Nodes
  /\ \A u \in Nodes: \A v \in Nodes: (<<u, v>> \in Adj) <=> (<<v, u>> \in Adj)
  /\ \A u \in Nodes: ~(<<u, u>> \in Adj)
  /\ MaxCardinality \in Nat

VARIABLES mom, dist

DistRange == 0..MaxCardinality

Neighbors(n) == { m \in Nodes : <<n, m>> \in Adj }

Init ==
  /\ mom = [ n \in Nodes |-> n ]
  /\ dist = [ n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality ]

Next ==
  \E v \in Nodes \ {Root}:
    \E u \in Neighbors(v):
      LET lo == dist[u]
          hi == dist[v]
      IN /\ lo + 1 < hi
         /\ \E k \in DistRange:
              /\ lo < k
              /\ k < hi
              /\ mom' = [mom EXCEPT ![v] = u]
              /\ dist' = [dist EXCEPT ![v] = k]

vars == << mom, dist >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Terminated ==
  \A v \in Nodes \ {Root}:
    \A u \in Neighbors(v):
      dist[v] <= dist[u] + 1

IsRootedSpanningTree ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> DistRange]
  /\ mom[Root] = Root
  /\ dist[Root] = 0
  /\ \A v \in Nodes \ {Root}:
       /\ <<v, mom[v]>> \in Adj
       /\ dist[mom[v]] < dist[v]
       /\ dist[v] \in 1..MaxCardinality

Safety == [](Terminated => IsRootedSpanningTree)

Liveness == <> Terminated

EventualRootParent ==
  \A v \in Nodes \ {Root}: <> (mom[v] = Root)

=============================================================================