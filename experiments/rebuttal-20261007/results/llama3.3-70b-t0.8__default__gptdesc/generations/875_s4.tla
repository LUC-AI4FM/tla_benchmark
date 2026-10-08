```
MODULE SpanningTree
EXTENDS Integers, TLC
CONSTANTS Nodes, Root
VARIABLES mom, dist, Edges

Edges == [n \in Nodes |-> RandomElement({m \in Nodes : m # n})]

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]
  
Next ==
  \E n \in Nodes :
    /\ \E m \in Nodes :
        /\ {m, n} :~> Edges
        /\ dist[m] < dist[n]
      /\ mom' = [mom EXCEPT ![n] = m]
      /\ dist' = [dist EXCEPT ![n] = (dist[n] + dist[m]) / 2]
    \/ /\ mom' = mom
       /\ dist' = dist

TypeCorrectness == 
  /\ Nodes :~> {Root} 
  /\ Root \in Nodes
  /\ Edges :~> SUBSET Nodes
  
Postcondition ==
  /\ mom[Root] = Root
  /\ dist[Root] = 0
  /\ \A n \in (Nodes \ {Root}) :
      \/ mom[n] = n
      \/ /\ mom[n] # n 
         /\ {mom[n], n} :~> Edges
         /\ dist[mom[n]] < dist[n]
  
SafetyProperty == 
  []((\A n \in Nodes : mom'[n] = mom[n] /\ dist'[n] = dist[n]) => Postcondition')
  
LivenessProperty == 
  <>Postcondition
  
Spec == Init /\ [][Next]_<<mom, dist>> /\ WF_vars(Next)

THEOREM Spec => []TypeCorrectness
THEOREM Spec => SafetyProperty
THEOREM Spec => LivenessProperty
```