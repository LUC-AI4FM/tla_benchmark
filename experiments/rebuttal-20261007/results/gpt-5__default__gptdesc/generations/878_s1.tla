------------------------------- MODULE RootedSpanningTree -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS NODES, Root, Adj, MaxCardinality

ASSUME
  /\ NODES # {}
  /\ Root \in NODES
  /\ Adj \in [NODES -> SUBSET NODES]
  /\ \A v \in NODES: \A u \in Adj[v]: v \in Adj[u]
  /\ MaxCardinality \in Nat
  /\ MaxCardinality >= Cardinality(NODES)

VARIABLES mom, dist

DistRange == 0..MaxCardinality

Init ==
  /\ mom = [n \in NODES |-> n]
  /\ dist = [n \in NODES |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next ==
  \E v \in NODES:
    \E u \in Adj[v]:
      /\ dist[u] < dist[v]
      /\ \E d \in 0..(dist[v] - 1):
         /\ mom' = [mom EXCEPT ![v] = u]
         /\ dist' = [dist EXCEPT ![v] = d]

vars == << mom, dist >>

Terminated ==
  \A v \in NODES: \A u \in Adj[v]: dist[u] >= dist[v]

RECURSIVE Ancestor(_, _)
Ancestor(v, k) ==
  IF k = 0 THEN v ELSE mom[Ancestor(v, k - 1)]

ReachRoot(v) ==
  \E k \in 0..Cardinality(NODES): Ancestor(v, k) = Root

Post ==
  /\ mom[Root] = Root
  /\ \A v \in NODES \ {Root}: mom[v] \in Adj[v]
  /\ \A v \in NODES: ReachRoot(v)

TypeInv ==
  /\ mom \in [NODES -> NODES]
  /\ dist \in [NODES -> DistRange]

Safety ==
  [](Terminated => Post)

Termination ==
  <>Terminated

EventuallyRootParent ==
  \A v \in NODES: <>(mom[v] = Root)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

========================================================================================