------------------------------- MODULE SpanningTree -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root

VARIABLES mom, dist

Edges == [n \in Nodes |-> RandomElement({s \in SUBSET (Nodes \ {n}) : s \subseteq Nodes})]

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE +\infty]

Next ==
    LET neighbors == [n \in Nodes |-> {m \in Edges[n] : dist[m] < dist[n]}]
    IN \/ /\ \E n \in Nodes : 
              /\ mom'[n] \in neighbors[n]
              /\ dist'[n] = dist[mom'[n]] + 1
           /\ \A m \notin Nodes : UNCHANGED mom[m]
              /\ UNCHANGED dist[m]

RootedSpanningTree ==
    LET tree == [n \in Nodes |-> CHOOSE p \in SUBSET Nodes : n \in p /\ (\A q \in p : mom[q] = IF q = Root THEN q ELSE p[\{q}])]
    IN  /\ \A n \in Nodes : tree[n] \subseteq Nodes
        /\ \A n \in Nodes : Root \in tree[n]
        /\ \A n \in Nodes, m \in Nodes : n \in tree[m] => m \in tree[n]
        /\ \A n \in Nodes : Cardinality(tree[n]) = Cardinality(Nodes)

Quiescence ==
    /\ \A n \in Nodes : mom'[n] = mom[n]
       /\ dist'[n] = dist[n]

Spec ==
    /\ Init
    /\ [][Next]_<<mom, dist>>
    /\ WF_vars(Next)
    /\ <>(RootedSpanningTree \/ Quiescence)

=============================================================================