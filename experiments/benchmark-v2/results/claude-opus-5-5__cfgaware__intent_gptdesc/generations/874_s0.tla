------------------------------ MODULE SpanningTree ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality

NodesVal == {1, 2, 3, 4}
EdgesVal == {{1, 2}, {1, 3}, {2, 3}, {3, 4}}
RootVal  == 1

ASSUME /\ Root \in Nodes
       /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
       /\ MaxCardinality \in Nat

VARIABLES mom, dist

vars == <<mom, dist>>

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

TypeOK == /\ mom  \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> Nat]

Init == /\ mom  = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next == \E n \in Nodes :
          \E m \in Nbrs(n) :
             /\ dist[m] < 1 + dist[n]
             /\ \E d \in (dist[m] + 1) .. (dist[n] - 1) :
                   /\ dist' = [dist EXCEPT ![n] = d]
                   /\ mom'  = [mom  EXCEPT ![n] = m]

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Shortest-path distances from the root in the graph
Reach[k \in 0 .. Cardinality(Nodes)] ==
    IF k = 0 THEN {Root}
    ELSE Reach[k - 1] \cup {n \in Nodes : \E m \in Reach[k - 1] : {m, n} \in Edges}

Distance(n) ==
    CHOOSE d \in 0 .. Cardinality(Nodes) :
        /\ n \in Reach[d]
        /\ (d = 0) \/ (n \notin Reach[d - 1])

\* Safety properties
RootInv == /\ mom[Root] = Root
           /\ dist[Root] = 0

ParentIsNeighbor == \A n \in Nodes \ {Root} :
                       (mom[n] = n) \/ (mom[n] \in Nbrs(n))

NoCycles == \A n \in Nodes \ {Root} :
               (mom[n] # n) => (dist[mom[n]] < dist[n])

DistBound == \A n \in Nodes : dist[n] <= MaxCardinality

Inv == /\ TypeOK
       /\ RootInv
       /\ ParentIsNeighbor
       /\ NoCycles
       /\ DistBound

\* Stabilized spanning tree with correct distances
PostCondition ==
    \A n \in Nodes :
       IF n = Root
         THEN /\ mom[n] = Root
              /\ dist[n] = 0
         ELSE /\ mom[n] \in Nbrs(n)
              /\ dist[n] = Distance(n)
              /\ dist[n] = dist[mom[n]] + 1

Safety == []Inv

Liveness == <>[]PostCondition

Termination == <>(ENABLED <<Next>>_vars = FALSE)
=============================================================================