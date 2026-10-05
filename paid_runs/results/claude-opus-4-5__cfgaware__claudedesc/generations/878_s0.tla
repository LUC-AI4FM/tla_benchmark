---------------------------- MODULE SpanningTree ----------------------------

CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME /\ Root \in Nodes
       /\ \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

VARIABLES mom, dist

vars == <<mom, dist>>

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> 0..MaxCardinality]

Init == /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
        /\ mom = [n \in Nodes |-> n]

Update(n, m) ==
    /\ {n, m} \in Edges
    /\ dist[m] + 1 < dist[n]
    /\ \E d \in (dist[m] + 1)..(dist[n] - 1) :
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ mom' = [mom EXCEPT ![n] = m]

Next == \E n \in Nodes : \E m \in Nodes : Update(n, m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Postcondition ==
    /\ dist[Root] = 0
    /\ mom[Root] = Root
    /\ \A n \in Nodes :
        IF dist[n] = MaxCardinality
        THEN /\ mom[n] = n
             /\ \A m \in Neighbors(n) : dist[m] = MaxCardinality
        ELSE IF n # Root
             THEN /\ mom[n] \in Neighbors(n)
                  /\ dist[n] = dist[mom[n]] + 1
             ELSE TRUE

Safety == (~ENABLED Next) => Postcondition

Terminated == ~ENABLED Next

Liveness == <>Terminated

=============================================================================