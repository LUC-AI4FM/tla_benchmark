---------------------------- MODULE SpanningTree ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality
VARIABLES mom, dist

Assume == 
  /\ Root \in Nodes
  /\ Edges \subseteq {x \in SUBSET Nodes : Cardinality(x) = 2}
  /\ MaxCardinality \in Nat
  /\ Cardinality(Nodes) <= MaxCardinality

Init ==
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
  /\ mom = [n \in Nodes |-> n]

Next ==
  \E n \in Nodes, m \in Nodes :
    /\ {n, m} \in Edges
    /\ dist[m] + 1 < dist[n]
    /\ \E d \in (dist[m] + 1)..(dist[n] - 1) :
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ mom' = [mom EXCEPT ![n] = m]

Spec == 
  /\ Init
  /\ [][Next]_<<mom, dist>>
  /\ WF_<<mom, dist>>(Next)

Postcondition ==
  /\ dist[Root] = 0
  /\ mom[Root] = Root
  /\ \A n \in Nodes :
      \/ dist[n] = MaxCardinality 
        /\ mom[n] = n 
        /\ \A m \in Nodes : {n, m} \in Edges => dist[m] = MaxCardinality
      \/ dist[n] = dist[mom[n]] + 1 
        /\ {n, mom[n]} \in Edges

TypeOK == 
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> 0..MaxCardinality]

Safety == []<>(Postcondition)

Liveness == <>Postcondition

=============================================================================