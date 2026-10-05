---------------------------- MODULE SpanningTreeRandom ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root, MaxCardinality

ASSUME Root \in Nodes
ASSUME MaxCardinality \in Nat /\ MaxCardinality >= Cardinality(Nodes)

PotentialNeighbors(n) == Nodes \ {n}

RandomNeighbors(n) == RandomElement(SUBSET PotentialNeighbors(n))

Edges == [n \in Nodes |-> RandomNeighbors(n)]

Neighbors(n) == {m \in Nodes : m \in Edges[n] \/ n \in Edges[m]}

VARIABLES mom, dist

vars == <<mom, dist>>

TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> 0..MaxCardinality]

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

CanImprove(n, m) == /\ m \in Neighbors(n)
                    /\ dist[m] < dist[n] - 1

Improve(n, m) == /\ CanImprove(n, m)
                 /\ \E d \in (dist[m] + 1)..(dist[n] - 1):
                      dist' = [dist EXCEPT ![n] = d]
                 /\ mom' = [mom EXCEPT ![n] = m]

Next == \E n \in Nodes : \E m \in Nodes : Improve(n, m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

PostCondition == 
    \A n \in Nodes :
        \/ (n = Root /\ dist[n] = 0)
        \/ (dist[n] = MaxCardinality /\ \A m \in Neighbors(n) : dist[m] = MaxCardinality)
        \/ (dist[n] = dist[mom[n]] + 1 /\ mom[n] \in Neighbors(n))

Safety == (~ENABLED Next) => PostCondition

Liveness == <>PostCondition

=============================================================================