----------------------------- MODULE SpanningTree -----------------------------
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality

(*
  Assumptions about the graph and bounds, plus a concrete instantiation:
  - Root ∈ Nodes
  - Each edge is a 2-element subset of Nodes (undirected simple graph)
  - MaxCardinality is a natural number and >= Cardinality(Nodes)
  - Concrete model: 5 nodes, 7 edges, connected, Root = "n1"
*)
ASSUME
  /\ Root \in Nodes
  /\ Edges \subseteq { e \in SUBSET Nodes : Cardinality(e) = 2 }
  /\ MaxCardinality \in Nat
  /\ Cardinality(Nodes) \leq MaxCardinality
  /\ Nodes = {"n1","n2","n3","n4","n5"}
  /\ Edges =
       { {"n1","n2"}, {"n1","n3"}, {"n2","n3"},
         {"n2","n4"}, {"n3","n4"}, {"n3","n5"}, {"n4","n5"} }
  /\ Root = "n1"
  /\ MaxCardinality = 10

VARIABLES mom, dist

vars == << mom, dist >>

DistRange == 0..MaxCardinality

Neighbor(m, n) ==
  /\ m \in Nodes
  /\ n \in Nodes
  /\ m # n
  /\ {m, n} \in Edges

Nbrs(S) == { n \in Nodes : \E m \in S : Neighbor(m, n) }

NbrsOf(n) == { m \in Nodes : Neighbor(m, n) }

RECURSIVE BFS(_)
BFS(k) ==
  IF k = 0
  THEN {Root}
  ELSE BFS(k - 1) \cup Nbrs(BFS(k - 1))

Reach == UNION { BFS(k) : k \in Nat }

TypeOK ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> DistRange]

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next ==
  \E n \in Nodes:
    \E m \in Nodes:
      \E d \in DistRange:
        /\ Neighbor(m, n)
        /\ dist[m] + 1 < dist[n]
        /\ dist[m] + 1 \leq d
        /\ d < dist[n]
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ mom'  = [mom  EXCEPT ![n] = m]

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

RootOk ==
  /\ dist[Root] = 0
  /\ mom[Root] = Root

UnreachablesOk ==
  \A n \in Nodes \ Reach:
    /\ dist[n] = MaxCardinality
    /\ mom[n] = n
    /\ \A m \in Nodes : Neighbor(m, n) => dist[m] = MaxCardinality

ReachablesOk ==
  \A n \in Reach \ {Root} :
    /\ Neighbor(mom[n], n)
    /\ dist[n] = dist[mom[n]] + 1

Post == RootOk /\ UnreachablesOk /\ ReachablesOk

EnabledNext == ENABLED Next

Safety == [](~EnabledNext => Post)

Liveness == <><>[](~EnabledNext)

=============================================================================