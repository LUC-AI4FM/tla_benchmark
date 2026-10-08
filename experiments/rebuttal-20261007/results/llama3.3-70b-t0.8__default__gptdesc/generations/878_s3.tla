```
MODULE RootedSpanningTree
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Root, MaxCardinality

VARIABLES mom, dist

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [Root |-> 0] \cup [n \in Nodes \ {Root} |-> MaxCardinality]

Next ==
  /\ \E n \in Nodes, m \in Nodes :
      /\ (m = mom[n]) 
      /\ (dist[m] < dist[n])
      /\ mom' = [mom EXCEPT ![n] = m]
      /\ dist' = [dist EXCEPT ![n] = someNewDist \in (dist[m] .. dist[n]-1)]
  /\ UNCHANGED <<mom, dist>> 

Spec ==
  Init /\ [][Next]_<<mom, dist>>
 WF_vacuous(Next, <<mom, dist>>)

THEOREM Spec => []<>Terminated
THEOREM Spec => [](Terminated => CorrectTree(mom))
THEOREM Spec => []<>(\A n \in Nodes : mom[n] = Root)

CorrectTree(parent) == 
  /\ Root \in Nodes 
  /\ parent[Root] = Root 
  /\ \A n \in Nodes \ {Root} : parent[n] \in Nodes 
  /\ \A n, m \in Nodes : parent[n] = m => m /= n
  /\ \A n, m, p \in Nodes : parent[n] = m /\ parent[m] = p => parent[n] = p

Terminated == 
  /\ mom = [n \in Nodes |-> Root]
```