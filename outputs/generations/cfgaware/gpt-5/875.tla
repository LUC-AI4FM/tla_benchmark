---- MODULE RandomizedSpanningTree ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root

VARIABLES mom, dist

vars == << mom, dist >>

Infinity == Cardinality(Nodes) + 1
DistValues == 0..Infinity

Edges ==
  LET Out == [ u \in Nodes |-> RandomSubset(Nodes \ {u}) ] IN
    { <<u,v>> \in Nodes \X Nodes :
        u /= v /\ (v \in Out[u] \/ u \in Out[v]) }

Edge(u, v) == <<u, v>> \in Edges

Init ==
  /\ mom = [u \in Nodes |-> u]
  /\ dist = [u \in Nodes |-> IF u = Root THEN 0 ELSE Infinity]

Next ==
  \E u \in Nodes:
    \E v \in Nodes:
      /\ Edge(u, v)
      /\ dist[v] + 1 < dist[u]
      /\ mom' = [mom EXCEPT ![u] = v]
      /\ dist' = [dist EXCEPT ![u] = dist[v] + 1]

TypeOK ==
  /\ Root \in Nodes
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> DistValues]

RECURSIVE Frontier(_)
Frontier(n) ==
  IF n = 0
  THEN {Root}
  ELSE
    LET S == Frontier(n - 1) IN
      S \cup { w \in Nodes : \E z \in S : Edge(z, w) }

Reach == UNION { Frontier(n) : n \in Nat }

Post ==
  /\ mom[Root] = Root
  /\ dist[Root] = 0
  /\ \A u \in Nodes \ {Root} :
       IF u \in Reach
       THEN /\ Edge(u, mom[u])
            /\ dist[u] = dist[mom[u]] + 1
       ELSE /\ mom[u] = u
            /\ dist[u] = Infinity

Quiescent ==
  \A u \in Nodes :
    \A v \in Nodes :
      ~( Edge(u, v) /\ dist[v] + 1 < dist[u] )

Safety == [] (Quiescent => Post)

Liveness == <> Post

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====