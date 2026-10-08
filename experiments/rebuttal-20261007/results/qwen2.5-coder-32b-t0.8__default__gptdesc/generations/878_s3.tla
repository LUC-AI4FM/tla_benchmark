------------------------------ MODULE SpanningTree ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, MaxCardinality
VARIABLES mom, dist

Init == /\ mom \in [Nodes -> Nodes]
        /\ dist \in [Nodes -> Nat \cup {MaxCardinality}]
        /\ (\A n \in Nodes : mom[n] = n)
        /\ dist[Root] = 0
        /\ (\A n \in Nodes \ {Root} : dist[n] = MaxCardinality)

Next == \/ CHOOSE u \in Nodes, v \in Nodes :
              /\ mom[u] # v
              /\ dist[v] < dist[u]
              -> \E d \in Nat : 1 <= d /\ d < dist[u] /\ 
                 /\ mom' = [mom EXCEPT ![u] = v]
                 /\ dist' = [dist EXCEPT ![u] = d]
          \/ UNCHANGED <<mom, dist>>

CorrectTree == /\ (\A n \in Nodes : Reachable(n, Root))
               /\ (\A n \in Nodes \ {Root} : mom[n] \in Nodes)
               /\ (\A n \in Nodes \ {Root}, m \in Nodes :
                     mom[m] = n => dist[n] + 1 = dist[m])
               /\ (\A u, v \in Nodes :
                     u # v /\ mom[u] = mom[v] => dist[u] = dist[v])

Reachable(n, r) == \/ n = r
                   \/ \E p \in Nodes : p # n /\ Reachable(p, r) /\ mom[n] = p

Spec ==
  Init /\ [][Next]_<<mom, dist>> /\ WF_next(Next)
  
Termination == <>(\A n \in Nodes : dist[n] < MaxCardinality)

TemporalProperty == <>(\A n \in Nodes : mom[n] = Root)

THEOREM Spec => []<>(CorrectTree /\ Termination /\ TemporalProperty)
=============================================================================