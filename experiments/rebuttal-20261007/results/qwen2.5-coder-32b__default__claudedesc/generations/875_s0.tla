------------------------------- MODULE RandomSpanningTree -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root, MaxCardinality

ASSUME Root \in Nodes /\ MaxCardinality \in Nat /\ Cardinality(Nodes) <= MaxCardinality

VARIABLES mom, dist

Init == 
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next ==
  LET candidates == { <<n, m>> \in Nodes \X Nodes : m \in Edges[n] /\ dist[m] + 1 < dist[n]}
  IN
    \/ candidates = {}
    \/ \E <<n, m>> \in candidates :
        /\ dist' = [dist EXCEPT ![n] = RandomElement({v \in (dist[m]+1)..(dist[n]-1) : v \in Nat})]
        /\ mom' = [mom EXCEPT ![n] = m]

Spec ==
  Init /\ [][Next]_<<mom, dist>> /\ WF_next(Next)

TypeOK ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> {0..MaxCardinality}]

PostCondition ==
  \A n \in Nodes :
    \/ (n = Root /\ dist[n] = 0)
    \/ (dist[n] = MaxCardinality /\ (\A m \in Edges[n] : dist[m] = MaxCardinality))
    \/ (dist[n] = dist[mom[n]] + 1)

Safety == [](TypeOK) /\ <>(~(Next)) => PostCondition

Liveness == <>[](PostCondition)

Edges ==
  [n \in Nodes |-> RandomElement({S \in SUBSET Nodes : n \notin S})]

=============================================================================