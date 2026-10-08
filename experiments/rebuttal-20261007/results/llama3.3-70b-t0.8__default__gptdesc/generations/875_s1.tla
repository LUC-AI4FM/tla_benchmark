```tla
MODULE SpanningTreeConstruction
EXTENDS Integers, TLC
CONSTANTS Nodes, Root
VARIABLES Edges, mom, dist

Edges == [n \in Nodes | RandomElement({m \in Nodes : m # n})]

Init ==
  /\ Edges = [n \in Nodes | {}]
  /\ mom = [n \in Nodes | n]
  /\ dist = [n \in Nodes | IF n = Root THEN 0 ELSE Infinity]

Next ==
  /\ Edges' = Edges
  /\ mom' = [mom EXCEPT !n = m]
  /\ dist' = [dist EXCEPT !n = d]
  /\ n \in Nodes
  /\ m \in Edges[n]
  /\ dist[m] < dist[n]
  /\ d \in (dist[m]+1)..(dist[n]-1)
  /\ mom'[n] = m

Postcondition ==
  /\ mom[Root] = Root
  /\ Root \in Domain mom
  /\ \A n \in Nodes \ {Root} :
      \/ mom[n] = n
      \/ \E m \in Nodes : mom[m] = n /\ dist[m] < dist[n]
  /\ \A n, m \in Nodes : mom[n] = m => dist[n] > dist[m]

TypeCorrectness == 
  /\ Nodes \subseteq Nat
  /\ Root \in Nodes

SafetyInvariant ==
  TypeCorrectness
  /\ Postcondition

Spec ==
  /\ Init
  /\ [][Next]_Edges
  /\ WF_vars(Next)

THEOREM Spec => []Postcondition
```