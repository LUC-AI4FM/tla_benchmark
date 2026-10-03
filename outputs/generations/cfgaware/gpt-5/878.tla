------------------------------ MODULE RootedSpanningTree ------------------------------

EXTENDS Naturals

CONSTANTS
  Node,             \* Finite set of nodes
  Root,             \* Distinguished root node
  Adj,              \* Undirected edge relation: subset of Node \X Node
  MaxCardinality    \* Finite stand-in for "infinity" in distance values

ASSUME Root \in Node
ASSUME /\ Adj \subseteq Node \X Node
       /\ \A u, v \in Node : <<u, v>> \in Adj => <<v, u>> \in Adj
ASSUME MaxCardinality \in Nat \ {0}

VARIABLES mom, dist

Neighbors(n) == { m \in Node : <<n, m>> \in Adj }

TypeOK ==
  /\ mom \in [Node -> Node]
  /\ dist \in [Node -> 0..MaxCardinality]

Init ==
  /\ mom = [ n \in Node |-> n ]
  /\ dist = [ n \in Node |-> IF n = Root THEN 0 ELSE MaxCardinality ]

Next ==
  \E u \in Node \ {Root} :
    \E v \in Neighbors(u) :
      /\ dist[v] + 1 < dist[u]
      /\ \E newDist \in (dist[v] + 1) .. (dist[u] - 1) :
           /\ mom' = [mom EXCEPT ![u] = v]
           /\ dist' = [dist EXCEPT ![u] = newDist]

vars == << mom, dist >>

Terminated ==
  \A u \in Node \ {Root} :
    \A v \in Neighbors(u) :
      dist[u] <= dist[v] + 1

Post ==
  /\ TypeOK
  /\ mom[Root] = Root
  /\ dist[Root] = 0
  /\ \A u \in Node \ {Root} :
       /\ mom[u] \in Neighbors(u)
       /\ dist[u] = dist[mom[u]] + 1

Safety == [] (Terminated => Post)

Liveness ==
  /\ <> Terminated
  /\ \A n \in Node : <> (mom[n] = Root)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

==============================