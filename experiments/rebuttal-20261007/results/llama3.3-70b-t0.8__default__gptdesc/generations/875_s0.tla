```
MODULE SpanningTree
EXTENDS Integers, TLC
CONSTANTS Nodes, Root
VARIABLES Edges, mom, dist

Edges == [n \in Nodes | RANDOM \subset (Nodes \ {n})]

Init ==
  /\ Edges = [n \in Nodes | {}]
  /\ mom = [n \in Nodes | n]
  /\ dist = [n \in Nodes | IF n = Root THEN 0 ELSE Infinity]

Next ==
  /\ Edges' = Edges
  /\ mom' = [mom EXCEPT !n = v]
  /\ dist' = [dist EXCEPT !n = d]
  /\ n \in Nodes
  /\ v \in Edges[n]
  /\ dist[v] < dist[n]
  /\ d \in (dist[n] + 1 .. dist[v])

TypeOK == 
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> Nat \cup {Infinity}]
  /\ Edges \in [Nodes -> SUBSET Nodes]

Postcondition == 
  /\ TypeOK
  /\ Root \in Nodes
  /\ mom[Root] = Root
  /\ dist[Root] = 0
  /\ (\A n \in Nodes \ {Root} : 
        IF mom[n] /= n THEN mom[n] \in Nodes /\ dist[mom[n]] < dist[n])
  /\ (\A n \in Nodes \ {Root} : 
        IF dist[n] /= Infinity THEN dist[n] > 0)

Safety == 
  /\ TypeOK
  /\ (\A n \in Nodes : mom[n] = n => dist[n] = Infinity)
  /\ (\A n \in Nodes : dist[n] < Infinity => mom[n] /= n)

Spec ==
  /\ Init
  /\ [][Next]_Edges
  /\ WF_vars(Next)

THEOREM Spec => []Postcondition
```