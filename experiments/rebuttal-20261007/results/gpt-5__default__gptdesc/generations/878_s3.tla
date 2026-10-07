----------------------------- MODULE RootedSpanningTree -----------------------------

EXTENDS Integers, Naturals, FiniteSets

CONSTANTS
  Nodes,             \* nonempty finite set of nodes
  Edges,             \* undirected edge relation: subset of Nodes × Nodes
  Root,              \* distinguished root node
  MaxCardinality     \* finite stand-in for infinity (a natural number)

ASSUME
  /\ Nodes # {} /\ IsFiniteSet(Nodes)
  /\ Root \in Nodes
  /\ Edges \subseteq Nodes \X Nodes
  /\ \A u,v \in Nodes : (<<u,v>> \in Edges) <=> (<<v,u>> \in Edges)   \* symmetry
  /\ \A v \in Nodes : <<v,v>> \notin Edges                            \* no self-loops
  /\ MaxCardinality \in Nat
  /\ MaxCardinality >= Cardinality(Nodes) - 1

VARIABLES mom, dist

Adj(u,v) ==
  <<u,v>> \in Edges

DistRange == 0..MaxCardinality

TypeOK ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> DistRange]

Init ==
  /\ mom = [v \in Nodes |-> v]
  /\ dist = [v \in Nodes |-> IF v = Root THEN 0 ELSE MaxCardinality]

Next ==
  \E v \in Nodes, u \in Nodes, newDist \in DistRange :
    /\ Adj(u,v)
    /\ dist[u] < dist[v]
    /\ dist[u] < newDist /\ newDist < dist[v]
    /\ mom'  = [mom  EXCEPT ![v] = u]
    /\ dist' = [dist EXCEPT ![v] = newDist]

vars == << mom, dist >>

Terminated ==
  ~ENABLED Next

Postcondition ==
  /\ TypeOK
  /\ dist[Root] = 0
  /\ mom[Root] = Root
  /\ \A v \in Nodes \ {Root} :
       /\ Adj(v, mom[v])
       /\ dist[v] = dist[mom[v]] + 1

\* Safety: termination implies the rooted spanning tree postcondition
Safety ==
  [](Terminated => Postcondition)

\* Liveness: eventual termination (and remaining terminated thereafter)
Termination ==
  <>[] Terminated

\* Additional temporal property: every node eventually has Root as its parent
AllToRoot ==
  \A v \in Nodes \ {Root} : <> (mom[v] = Root)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

================================================================================