```tla
MODULE SpanningTreeAlgorithm

EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME 
  /\ Root \in Nodes
  /\ \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2
  /\ MaxCardinality \in Nat /\ Cardinality(Nodes) <= MaxCardinality

VARIABLES mom, dist

Init == 
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
  /\ mom = [n \in Nodes |-> n]

Next == 
  \E n \in Nodes, m \in Nodes : 
    /\ {m, n} \in Edges
    /\ dist[m] + 1 < dist[n]
    /\ \E d \in Nat : 
        /\ dist[m] + 1 <= d
        /\ d < dist[n]
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ mom' = [mom EXCEPT ![n] = m]

Spec == Init /\ [][Next]_<<mom, dist>> /\ WF_<<mom, dist>>(Next)

TypeOK == 
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> Nat]

Safety == 
  TypeOK /\ 
  (\A n \in Nodes : 
    IF n = Root THEN dist[n] = 0 /\ mom[n] = n
    ELSE IF dist[n] = MaxCardinality THEN mom[n] = n /\ \A m \in Nodes : {m, n} \in Edges => dist[m] = MaxCardinality
    ELSE dist[n] = dist[mom[n]] + 1 /\ {mom[n], n} \in Edges)

Liveness == <>[]<<Safety>>_dist

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety => Liveness

```
Note: The `THEOREM` statements are used to specify the properties that should be checked by the model checker. In this case, we want to check that `Spec` implies `[]TypeOK` (type correctness is an invariant) and that `Spec` implies `[]Safety => Liveness` (if safety is always true, then liveness holds).