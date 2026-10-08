```
MODULE ShortestPathSpanningTree
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, Root
VARIABLES parent, distance

Init ==
  /\ parent = [n \in Nodes |-> IF n = Root THEN n ELSE n]
  /\ distance = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]

Next ==
  \/ \E n \in Nodes :
      /\ distance[n] # 0
      /\ \E m \in Nodes :
          /\ {m, n} \in Edges
          /\ distance[m] < distance[n]
          /\ parent' = [parent EXCEPT ![n] = m]
          /\ distance' = [distance EXCEPT ![n] = distance[m] + 1]
      \/ \E n \in Nodes :
          /\ distance[n] = Infinity
          /\ \E m \in Nodes :
              /\ {m, n} \in Edges
              /\ distance[m] # Infinity
              /\ parent' = [parent EXCEPT ![n] = m]
              /\ distance' = [distance EXCEPT ![n] = distance[m] + 1]
      \/ \E n \in Nodes :
          /\ distance[n] # Infinity
          /\ \A m \in Nodes : {m, n} \in Edges => distance[m] >= distance[n]
          /\ parent' = parent
          /\ distance' = distance

Spec ==
  /\ Init
  /\ [][Next]_<<parent, distance>>
  /\ WF_<<parent, distance>>(Next)

THEOREM Spec => [](/\
  /\ \A n \in Nodes : parent[n] \in {m \in Nodes : {m, n} \in Edges} \cup {n}
  /\ \A n \in Nodes : distance[n] \in Nat \cup {Infinity}
  /\ \A n \in Nodes : distance[n] # Infinity => distance[n] = distance[parent[n]] + 1
  /\ Root \in Nodes
  /\ parent[Root] = Root
  /\ distance[Root] = 0
  /\ \A n \in Nodes : distance[n] = Infinity => parent[n] = n
)

THEOREM Spec => <>(\A n \in Nodes :
  /\ (n = Root)
  \/ (distance[n] = Infinity /\ \A m \in Nodes : {m, n} \in Edges => distance[m] = Infinity)
  \/ (distance[n] # Infinity /\ parent[n] \in {m \in Nodes : {m, n} \in Edges} /\ distance[n] = distance[parent[n]] + 1)
)

THEOREM Spec => SF_<<parent, distance>>(Next)
```