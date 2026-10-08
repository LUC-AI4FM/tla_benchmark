----------------------------- MODULE SPTree -----------------------------
EXTENDS Naturals

CONSTANTS
  NODES, \* Nonempty set of nodes
  Root,  \* Distinguished root in NODES
  INF    \* Special "infinite" distance value

ASSUME INF \notin Nat

VARIABLES
  Edge,   \* Undirected, static edge relation (set of ordered pairs)
  Parent, \* [NODES -> NODES]
  Dist    \* [NODES -> Nat \cup {INF}]

vars == << Edge, Parent, Dist >>

Neigh(n) == { m \in NODES : <<n,m>> \in Edge }

SymmetricEdge == \A u \in NODES, v \in NODES : (<<u,v>> \in Edge) => (<<v,u>> \in Edge)

TypeOK ==
  /\ Root \in NODES
  /\ Edge \subseteq NODES \X NODES
  /\ SymmetricEdge
  /\ Parent \in [NODES -> NODES]
  /\ Dist \in [NODES -> (Nat \cup {INF})]

Init ==
  /\ Root \in NODES
  /\ Edge \subseteq NODES \X NODES
  /\ SymmetricEdge
  /\ Parent = [ n \in NODES |-> n ]
  /\ Dist   = [ n \in NODES |-> IF n = Root THEN 0 ELSE INF ]

NodeImprove(n, m) ==
  /\ n \in NODES
  /\ n # Root
  /\ m \in Neigh(n)
  /\ Dist[m] \in Nat
  /\ (Dist[n] = INF \/ (Dist[n] \in Nat /\ Dist[n] > Dist[m] + 1))

Update(n, m) ==
  /\ NodeImprove(n, m)
  /\ Parent' = [Parent EXCEPT ![n] = m]
  /\ Dist'   = [Dist   EXCEPT ![n] = Dist[m] + 1]
  /\ Edge'   = Edge

NodeStep(n) == \E m \in NODES : Update(n, m)

Next == \E n \in NODES : NodeStep(n)

Fairness == \A n \in NODES : SF_vars(NodeStep(n))

Spec == Init /\ [][Next]_vars /\ Fairness

ParentNeighborOrSelf ==
  \A n \in NODES : (Parent[n] = n) \/ (<<n, Parent[n]>> \in Edge)

DistanceOK ==
  \A n \in NODES : Dist[n] \in (Nat \cup {INF})

RootOK ==
  /\ Parent[Root] = Root
  /\ Dist[Root] = 0

FiniteParentRelation ==
  \A n \in NODES :
    (Dist[n] \in Nat /\ Dist[n] > 0)
      => (Parent[n] # n /\ <<n, Parent[n]>> \in Edge
          /\ Dist[Parent[n]] \in Nat
          /\ Dist[n] = Dist[Parent[n]] + 1)

UnreachedInvariant ==
  \A n \in NODES :
    (Dist[n] = INF /\ \A m \in Neigh(n) : Dist[m] = INF) => Parent[n] = n

NoZeroForNonRoot ==
  \A n \in NODES : n # Root => Dist[n] # 0

Safety ==
  [] ( TypeOK
       /\ RootOK
       /\ ParentNeighborOrSelf
       /\ DistanceOK
       /\ FiniteParentRelation
       /\ UnreachedInvariant
       /\ NoZeroForNonRoot )

CanImprove(n) ==
  /\ n \in NODES
  /\ n # Root
  /\ \E m \in Neigh(n) :
        Dist[m] \in Nat /\ (Dist[n] = INF \/ (Dist[n] \in Nat /\ Dist[n] > Dist[m] + 1))

Stable == \A n \in NODES : ~CanImprove(n)

PostOK ==
  \A n \in NODES :
    \/ n = Root
    \/ (Dist[n] = INF /\ Parent[n] = n /\ \A m \in Neigh(n) : Dist[m] = INF)
    \/ (Dist[n] \in Nat /\ Dist[n] > 0
        /\ <<n, Parent[n]>> \in Edge
        /\ Dist[Parent[n]] \in Nat
        /\ Dist[n] = Dist[Parent[n]] + 1)

Liveness == <>[] (Stable /\ PostOK)

=============================================================================