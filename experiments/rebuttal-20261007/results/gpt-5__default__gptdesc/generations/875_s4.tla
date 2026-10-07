----------------------------- MODULE RandomizedSpanningTree -----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root

ASSUME /\ Root \in Nodes
       /\ IsFiniteSet(Nodes)
       /\ Nodes # {}

(*
  Random undirected graph:
  For each node n, pick a random subset of the other nodes; symmetrize to make the edge relation undirected.
*)
MNeighbors == [ n \in Nodes |-> RandomElement(SUBSET (Nodes \ {n})) ]

Neighbors == [ n \in Nodes |-> (MNeighbors[n] \cup { m \in Nodes : n \in MNeighbors[m] }) \ {n} ]

Edges == { {u, v} : u \in Nodes, v \in Neighbors[u], u # v }

Edge(u, v) == u # v /\ {u, v} \in Edges

Inf == "Inf"
DistDom == Nat \cup {Inf}

VARIABLES mom, dist

vars == << mom, dist >>

TypeOK ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> DistDom]

Init ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> DistDom]
  /\ \A n \in Nodes : mom[n] = n
  /\ dist[Root] = 0
  /\ \A n \in Nodes \ {Root} : dist[n] = Inf

LtDist(a, b) ==
  /\ a \in Nat
  /\ (b = Inf \/ (b \in Nat /\ a < b))

BetweenSet(a, b) ==
  IF a \in Nat /\ b \in Nat THEN { k \in Nat : a < k /\ k < b }
  ELSE IF a \in Nat /\ b = Inf THEN { a + 1 }
  ELSE {}

Next ==
  \E n \in Nodes:
    \E q \in Nodes:
      \E newd \in DistDom:
        /\ Edge(n, q)
        /\ LtDist(dist[q], dist[n])
        /\ newd \in BetweenSet(dist[q], dist[n])
        /\ mom' = [mom EXCEPT ![n] = q]
        /\ dist' = [dist EXCEPT ![n] = newd]

RECURSIVE Close(_)
Close(S) ==
  LET T == S \cup { v \in Nodes : \E u \in S : Edge(u, v) }
  IN  IF T = S THEN S ELSE Close(T)

Reachable == Close({Root})

FiniteNodes == { n \in Nodes : dist[n] \in Nat }

Post ==
  /\ TypeOK
  /\ dist[Root] = 0
  /\ mom[Root] = Root
  /\ FiniteNodes = Reachable
  /\ \A u \in FiniteNodes :
        (u = Root) \/ (Edge(u, mom[u]) /\ dist[mom[u]] \in Nat /\ dist[u] = dist[mom[u]] + 1)
  /\ \A u \in Nodes \ FiniteNodes : mom[u] = u

EnabledNext ==
  \E n \in Nodes:
    \E q \in Nodes:
      \E newd \in DistDom:
        /\ Edge(n, q)
        /\ LtDist(dist[q], dist[n])
        /\ newd \in BetweenSet(dist[q], dist[n])

Quiescent == ~EnabledNext

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*
  Safety invariants and liveness properties to be checked against Spec.
*)
TypeInvariant == []TypeOK
Safety_QuiescenceImpliesPost == [](Quiescent => Post)
Liveness_EventualPost == <>Post

========================================================================================