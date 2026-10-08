------------------------------- MODULE SpanningTree -------------------------------

EXTENDS Naturals, TLC

CONSTANTS Nodes, Root

VARIABLES mom, dist

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE +\infty]

Edges ==
    LET RandomSubset(node) == {m \in (Nodes \ {node}): TLC!RandomElement({FALSE, TRUE})}
    IN [n \in Nodes |-> CHOOSE s \in SUBSET (Nodes \ {n}): s = RandomSubset(n)]

Next == 
    E <<n, m>> \in Edges :<<mom[n], dist[n]>> \in
        {<<m', d'>> \in [Nodes -> Nodes] /\ [Nodes -> Nat] :
            /\ m' = IF dist[m] < dist[n] THEN m ELSE mom[n]
            /\ d' = IF dist[m] < dist[n] THEN dist[m] + 1 ELSE dist[n]}

RootedSpanningTree ==
    LET Reachable == {n \in Nodes : n = Root \/ mom[n] # n}
        ParentsOK == \A n \in Nodes \ {Root} : mom[n] \in Nodes /\ n \notin Edges[mom[n]]
        DistancesOK == \A n \in Reachable : dist[n] <= Card(Nodes)
    IN
        /\ Reachable = Domain(mom) 
        /\ ParentsOK 
        /\ DistancesOK

Spec ==
    WF_vars(Next) /\ 
    Init /\ [][Next]_<<mom, dist>> /\ 
    <>(RootedSpanningTree)

=============================================================================