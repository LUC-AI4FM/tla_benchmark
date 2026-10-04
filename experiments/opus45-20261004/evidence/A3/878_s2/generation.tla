---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME Root \in Nodes
ASSUME MaxCardinality \in Nat
ASSUME MaxCardinality >= Cardinality(Nodes)

VARIABLES mom, dist

vars == <<mom, dist>>

Neighbors(n) == {m \in Nodes : {n, m} \in Edges \/ {m, n} \in Edges}

TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..MaxCardinality]

Init ==
    /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Update(n, m) ==
    /\ m \in Neighbors(n)
    /\ dist[m] < dist[n]
    /\ \E d \in (dist[m] + 1)..(dist[n] - 1) :
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ mom' = [mom EXCEPT ![n] = m]

Next ==
    \E n \in Nodes : \E m \in Nodes : Update(n, m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Terminated == ~ENABLED Next

ReachesRoot(n) ==
    LET RECURSIVE Path(_, _)
        Path(node, visited) ==
            IF node = Root THEN TRUE
            ELSE IF node \in visited THEN FALSE
            ELSE IF mom[node] = node THEN FALSE
            ELSE Path(mom[node], visited \cup {node})
    IN Path(n, {})

PostCondition ==
    /\ dist[Root] = 0
    /\ mom[Root] = Root
    /\ \A n \in Nodes :
        IF n = Root THEN TRUE
        ELSE
            /\ mom[n] \in Neighbors(n)
            /\ dist[n] = dist[mom[n]] + 1
            /\ ReachesRoot(n)

Safety == Terminated => PostCondition

Liveness == <>Terminated

EventuallyRootParent == \A n \in Nodes : <>(mom[n] = Root)

=============================================================================