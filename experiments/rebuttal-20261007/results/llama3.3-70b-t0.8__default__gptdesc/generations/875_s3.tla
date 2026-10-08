```tla
MODULE SpanningTree
EXTENDS Integers, TLC

CONSTANTS Nodes, Root
VARIABLES mom, dist, Edges

Edges == [n \in Nodes | {m \in Nodes : m # n}]

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]
  /\ Edges = [n \in Nodes |-> RandomElement({m \in Nodes : m # n})]

Next ==
  \E n \in Nodes :
    /\ mom[n] = n
    /\ \E neighbor \in Edges[n] :
      /\ dist[neighbor] < dist[n]
      /\ mom' = [mom EXCEPT ![n] = neighbor]
      /\ dist' = [dist EXCEPT ![n] = (dist[n] - 1)]

TypeOK == 
  /\ Nodes \subseteq DOMAIN mom
  /\ Nodes \subseteq DOMAIN dist

Postcondition ==
  TypeOK
  /\ \A n \in Nodes : IF n # Root THEN mom[n] \in Nodes
  /\ \A n \in Nodes : dist[n] >= 0

SafetyInv == 
  TypeOK
  /\ Postcondition

Quiescent == 
  \A n \in Nodes : ~\E neighbor \in Edges[n] : dist[neighbor] < dist[n]

Spec == 
  /\ Init
  /\ [][Next]_<<mom, dist, Edges>>
  /\ WF_vars(Next)

THEOREM Spec => []Postcondition
THEOREM Spec => <><Postcondition
```