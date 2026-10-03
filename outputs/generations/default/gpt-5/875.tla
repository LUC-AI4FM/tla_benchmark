----------------------------- MODULE RandomSpanningTree -----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Nodes,
  Root

ASSUME Root \in Nodes /\ Nodes # {}

VARIABLES mom, dist

MaxDist == Cardinality(Nodes)
DistVals == 0..MaxDist

Adjacency == [u \in Nodes |-> RandomElement(SUBSET(Nodes \ {u}))]

Edges ==
  { {u, v} : u \in Nodes, v \in Adjacency[u] } \cup
  { {u, v} : v \in Nodes, u \in Adjacency[v] }

IsEdge(u, v) == u # v /\ {u, v} \in Edges

Neighbors(u) == { v \in Nodes : IsEdge(u, v) }

IsPath(p) ==
  p \in Seq(Nodes)
  /\ Len(p) >= 1
  /\ \A i \in 1..(Len(p)-1) : IsEdge(p[i], p[i+1])

PathsTo(v) ==
  { p \in Seq(Nodes) :
      Len(p) >= 1
      /\ p[1] = Root
      /\ p[Len(p)] = v
      /\ IsPath(p)
  }

Reachable == { v \in Nodes : PathsTo(v) # {} }

MinDist(v) ==
  IF v \in Reachable
  THEN Min({ Len(p) - 1 : p \in PathsTo(v) })
  ELSE MaxDist

TypeOK ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> DistVals]
  /\ Root \in Nodes

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDist]

CanImprove(u) ==
  \E v \in Neighbors(u) : dist[v] + 2 <= dist[u]

Next ==
  \E u \in Nodes :
    \E v \in Neighbors(u) :
      /\ dist[v] + 2 <= dist[u]
      /\ \E d \in DistVals : dist[v] < d /\ d < dist[u]
      /\ mom' = [mom EXCEPT ![u] = v]
      /\ dist' = [dist EXCEPT ![u] = d]

vars == << mom, dist >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Post ==
  /\ TypeOK
  /\ dist[Root] = 0 /\ mom[Root] = Root
  /\ \A v \in Nodes :
       IF v \in Reachable THEN
         /\ dist[v] = MinDist(v)
         /\ (v = Root
             \/ (mom[v] \in Neighbors(v) /\ dist[mom[v]] = dist[v] - 1))
       ELSE
         /\ dist[v] = MaxDist
         /\ mom[v] = v

Quiescent == \A u \in Nodes : ~CanImprove(u)

Safety_QuiescenceImpliesPost == Quiescent => Post

Liveness_EventualPost == <>Post

=====================================================================================