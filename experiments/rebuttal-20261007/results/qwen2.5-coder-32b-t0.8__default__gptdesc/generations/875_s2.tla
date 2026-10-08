------------------------------ MODULE RandomSpanningTree ------------------------------

EXTENDS TLC, FiniteSets

CONSTANTS Nodes, Root

VARIABLES mom, dist

Edges == [n \in Nodes |-> RandomElement({s \in SUBSET (Nodes \ {n}) : s \subseteq Nodes})]

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE \infty]

Next ==
    LET newMom == [mom EXCEPT ![n] = CHOOSE m \in Edges[n] : dist[m] < dist[n]]
        newDist == [dist EXCEPT ![n] = LEAST d \in {d \in Nat : dist[newMom[n]] < d /\ d < dist[n]}]
    IN  \/ /\ n \in Nodes
            /\ newMom[n] /= mom[n]
            /\ newDist[n] < dist[n]
            /\ UNCHANGED <<mom EXCEPT ![n], dist EXCEPT ![n]>>
        \/ UNCHANGED <<mom, dist>>

Spec ==
    /\ Init
    /\ [][Next]_<<mom, dist>>
    /\ WF_vars(Next, <<mom, dist>>)

RootedTreeOrUnreachable ==
    LET Reachable == {n \in Nodes : dist[n] < \infty}
        TreeEdges == {(mom[n], n) \in Nodes \ {Root} X Nodes}
    IN  /\ \A u, v \in Reachable : Path(TreeEdges, u, v)
        /\ \A n \notin Reachable : dist[n] = \infty

Safety ==
    [](Reachable ==> RootedTreeOrUnreachable)

Liveness ==
    <>(\A n \in Nodes : dist[n] < \infty) \/ (\A n \notin Reachable : dist[n] = \infty)

=============================================================================