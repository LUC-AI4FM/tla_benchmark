------------------------------- MODULE SpanningTree -------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root

VARIABLES mom, dist

Edges == [n \in Nodes |-> RandomElement(SUBSET (Nodes \ {n}))]

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE +\infty]

Next ==
    \E n \in Nodes, m \in Edges[n] :
        \/ /\ dist[m] < dist[n]
           /\ mom' = [mom EXCEPT ![n] = m]
           /\ dist' = [dist EXCEPT ![n] = dist[m] + 1]
        \/ /\ dist[m] >= dist[n]
           /\ mom' = mom
           /\ dist' = dist

RootedTree ==
    LET reachable(n) == \E p \in Nodes : n \in {p} \cup (UNION {Edges[p]})
        path(n)     == <<n>> \o [k \in 1..dist[n] |-> mom[k]]
    IN  /\ \A n \in Nodes : n = Root \/ reachable(n)
        /\ \A n \in Nodes, p \in path(n), q \in path(n) :
                p = q \/ <<p>> \in SubSeq(q)

Safety == [](Next => RootedTree)

Liveness == <>(RootedTree)

Spec ==
    Init /\ [][Next]_<<mom, dist>> /\ WF_vars(Next)

=============================================================================