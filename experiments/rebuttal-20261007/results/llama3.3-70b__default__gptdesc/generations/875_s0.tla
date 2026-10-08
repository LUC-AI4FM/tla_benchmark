```
MODULE SpanningTree
EXTENDS Integers, TLC
CONSTANTS Nodes, Root
VARIABLES mom, dist, Edges

Edges == [n \in Nodes |-> RandomElement({m \in Nodes : m # n})]

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]
  /\ Edges = [n \in Nodes |-> {}]

Next ==
  /\ mom' = [mom EXCEPT !n = CHOOSE m \in Edges[n] : dist[m] < dist[n]]
  /\ dist' = [dist EXCEPT !n = (dist[n] + dist[mom'[n]]) / 2]
  /\ Edges' = Edges
  /\ n \in Nodes

TypeOK == 
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> Nat \cup {Infinity}]
  /\ Edges \in [Nodes -> SUBSET Nodes]

Postcondition ==
  /\ Root \in Nodes
  /\ TypeOK
  /\ mom[Root] = Root
  /\ dist[Root] = 0
  /\ \A n \in Nodes \ {Root} : 
      (mom[n] = n) \/ (dist[mom[n]] < dist[n])
  /\ \A n, m \in Nodes : mom[n] = m => m # n

Safety == 
  []((TypeOK) => Postcondition)

Liveness == 
  <>Postcondition

Spec == 
  Init /\ [][Next]_<<mom, dist, Edges>> /\ WF_vars(Next)
```