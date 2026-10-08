------------------------------- MODULE SpanningTreeAlgorithm -------------------------------

CONSTANTS Nodes, Root, MaxDistance

VARIABLES distances, parents

ASSUME Root \in Nodes
ASSUME MaxDistance >= CARD(Nodes)

TypeOK == 
    /\ distances \in [Nodes -> 0..MaxDistance]
    /\ parents   \in [Nodes -> Nodes]

Init ==
    /\ distances[Root] = 0
    /\ (\A n \in Nodes \ {Root} | distances[n] = MaxDistance)
    /\ (\A n \in Nodes        | parents[n] = n)

Next ==
    \E n \in Nodes, m \in Nodes : 
        \/ (distances[m] < distances[n] - 1) 
           /\ (distances[m] + 1 < distances[n])
           /\ (LET newDist == distances[m] + 1 IN
               /\ distances' = [distances EXCEPT ![n] = newDist]
               /\ parents'   = [parents EXCEPT ![n] = m])
        \/ UNCHANGED <<distances, parents>>

Spec ==
    Init /\ [][Next]_<<distances, parents>>

Safety ==
    \A n \in Nodes :
        \/ distances[n] = MaxDistance
        \/ (distances[n] = distances[parents[n]] + 1)

Liveness ==
    <>[](\A n \in Nodes : 
            \/ distances[n] = MaxDistance
            \/ (distances[n] = distances[parents[n]] + 1))

=============================================================================