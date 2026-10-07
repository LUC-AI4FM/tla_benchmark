```tla
MODULE SpanningTreeRandomizedTesting
EXTENDS Integers, TLC

CONSTANTS Nodes, Root, MaxCardinality

VARIABLES mom, dist

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Edges == {<<n, m>> : n, m \in Nodes, m \in RandomElement({m \in Nodes : m /= n})}

Next ==
  \E n \in Nodes, m \in Nodes :
    /\ {m} \subseteq Edges[n]
    /\ dist[m] < dist[n] - 1
    /\ mom' = [mom EXCEPT ![n] = m]
    /\ dist' = [dist EXCEPT ![n] = some d \in (dist[m]+1)..(dist[n]-1)]

Spec == Init /\ [][Next]_<<mom, dist>>
        /\ WF_<<mom, dist>>(Next)

TypeOK == mom \in [Nodes -> Nodes] /\ dist \in [Nodes -> Nat]

PostCondition ==
  \A n \in Nodes :
    (n = Root /\ dist[n] = 0)
    \/ (dist[n] = MaxCardinality
        /\ \A m \in Edges[n] : dist[m] = MaxCardinality)
    \/ (\E m \in Edges[n] : mom[n] = m /\ dist[n] = dist[m] + 1)

Safety == []PostCondition

Liveness == <>(PostCondition)

THEOREM Spec => []TypeOK
THEOREM Spec => Safety
THEOREM Spec => Liveness
```