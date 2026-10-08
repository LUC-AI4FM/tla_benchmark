```
MODULE SpanningTree
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, Root, Bound
VARIABLES parent, distance, messages

Init ==
  /\ parent = [n \in Nodes |-> IF n = Root THEN Root ELSE n]
  /\ distance = [n \in Nodes |-> IF n = Root THEN 0 ELSE Bound]
  /\ messages = {}

Next ==
  \/ \E n \in Nodes :
      /\ distance[n] /= 0
      /\ \E m \in Nodes : {n, m} \in Edges
      /\ \E d \in 0..Bound :
          /\ d < distance[n]
          /\ \A p \in Nodes : {p, n} \in Edges => d >= distance[p] + 1
          /\ parent' = [parent EXCEPT ![n] = CHOOSE m \in Nodes : {m, n} \in Edges /\ distance[m] = d - 1]
          /\ distance' = [distance EXCEPT ![n] = d]
          /\ messages' = messages \cup {<<n, d>>}
  \/ \E n \in Nodes, m \in Nodes, d \in 0..Bound :
      /\ {n, m} \in Edges
      /\ <<m, d>> \in messages
      /\ distance[n] > d + 1
      /\ parent' = [parent EXCEPT ![n] = m]
      /\ distance' = [distance EXCEPT ![n] = d + 1]
      /\ messages' = messages \ {<<m, d>>}

Spec ==
  /\ Init
  /\ [][Next]_<<parent, distance, messages>>
  /\ WF_<<parent, distance, messages>>(Next)

THEOREM Spec => [](\A n \in Nodes : 
  IF \E m \in Nodes : {n, m} \in Edges /\ distance[m] < Bound
  THEN parent[n] \in Nodes /\ {parent[n], n} \in Edges /\ distance[parent[n]] + 1 = distance[n]
  ELSE parent[n] = n)

THEOREM Spec => [](\A n \in Nodes : 
  IF distance[n] /= Bound 
  THEN \E m \in Nodes : {m, n} \in Edges /\ parent[m] = n)
```