---------------------------- MODULE RandomizedSpanningTree ----------------------------
EXTENDS Integers, TLC

CONSTANT Nodes, Root, MaxCardinality
VARIABLE mom, dist

AssumeRootInNodes == Root \in Nodes
AssumeMaxCardinality >= Cardinality(Nodes)

TypeOK == 
  /\ Assumptions
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> Nat]

Edges == {<<n, m>> : n \in Nodes, m \in RandomElement({x \in Nodes : x # n})}

Assumptions == 
  /\ AssumeRootInNodes
  /\ MaxCardinality >= Cardinality(Nodes)

Init == 
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next == 
  \E n \in Nodes, m \in Nodes :
    /\ {m, n} \subseteq Edges
    /\ dist[m] < dist[n] - 1
    /\ \E d \in (dist[m]+1)..(dist[n]-1) :
        /\ mom' = [mom EXCEPT ![n] = m]
        /\ dist' = [dist EXCEPT ![n] = d]

Spec == Init /\ [][Next]_<<mom, dist>> /\ WF_<<mom, dist>>(Next)

PostCondition == 
  \A n \in Nodes :
    (n = Root /\ dist[n] = 0) 
    \/ (dist[n] = MaxCardinality /\ \A m \in Nodes : {m, n} \subseteq Edges => dist[m] = MaxCardinality)
    \/ (\E m \in Nodes : mom[n] = m /\ dist[n] = dist[m] + 1)

Safety == []PostCondition
Liveness == PostCondition

THEOREM Spec => []TypeOK
THEOREM Spec => Safety
THEOREM Spec => Liveness
=============================================================================