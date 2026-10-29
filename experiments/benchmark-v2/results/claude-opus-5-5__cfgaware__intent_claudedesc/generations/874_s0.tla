------------------------------ MODULE SpanTree ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality

\* Concrete model values that the configuration substitutes for the constants
NodesVal == {1, 2, 3, 4, 5}
EdgesVal == {{1, 2}, {1, 3}, {2, 3}, {3, 4}, {4, 5}, {2, 5}}
RootVal  == 1

ASSUME Root \in Nodes
ASSUME \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
ASSUME MaxCardinality \in Nat

VARIABLES mom, dist
vars == <<mom, dist>>

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

TypeOK == /\ mom  \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> Nat]

Init == /\ mom  = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

\* A node n learns of a shorter path via neighbor m and adopts m as its parent
Next == \E n \in Nodes :
          \E m \in Nbrs(n) :
             /\ dist[m] < 1 + dist[n]
             /\ \E d \in (dist[m] + 1) .. (dist[n] - 1) :
                   /\ dist' = [dist EXCEPT ![n] = d]
                   /\ mom'  = [mom  EXCEPT ![n] = m]

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Correctness properties

\* Shortest distance from Root to n in the graph (computed by BFS levels)
RECURSIVE Reach(_, _)
Reach(S, k) == IF k = 0 THEN S
               ELSE LET T == Reach(S, k - 1)
                    IN  T \cup {m \in Nodes : \E t \in T : m \in Nbrs(t)}

ReachableFrom(r) == Reach({r}, Cardinality(Nodes))

Distance(n) == CHOOSE k \in 0 .. Cardinality(Nodes) :
                   /\ n \in Reach({Root}, k)
                   /\ \A j \in 0 .. (k - 1) : n \notin Reach({Root}, j)

RootProperty == mom[Root] = Root /\ dist[Root] = 0

\* Final (stable) state: a valid BFS spanning tree
PostCondition ==
  \A n \in Nodes :
     \/ /\ n = Root
        /\ dist[n] = 0
        /\ mom[n] = n
     \/ /\ n # Root
        /\ n \in ReachableFrom(Root)
        /\ dist[n] = Distance(n)
        /\ mom[n] \in Nbrs(n)
        /\ dist[n] = dist[mom[n]] + 1
     \/ /\ n \notin ReachableFrom(Root)
        /\ mom[n] = n
        /\ dist[n] = MaxCardinality

\* Invariant: once a node has a parent, its distance is consistent with it
Safety ==
  /\ RootProperty
  /\ \A n \in Nodes \ {Root} :
        mom[n] # n => /\ mom[n] \in Nbrs(n)
                      /\ dist[n] >= dist[mom[n]] + 1
                      /\ dist[n] >= Distance(n)

Terminated == ~ ENABLED Next

Liveness == <>[](PostCondition)

THEOREM Spec => []TypeOK
=============================================================================