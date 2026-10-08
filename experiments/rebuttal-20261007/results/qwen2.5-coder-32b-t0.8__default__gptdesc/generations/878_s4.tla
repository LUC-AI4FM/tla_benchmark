---- MODULE RootedSpanningTree ----

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Edges, Root, MaxCardinality
ASSUME Root \in Nodes
ASSUME \A u \in Nodes : \E v \in Nodes : <<u, v>> \in Edges \/ <<v, u>> \in Edges \/ u = Root
ASSUME MaxCardinality > 0

VARIABLES mom, dist

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next ==
    \E u \in Nodes :
      \E v \in Nodes :
        <<u, v>> \in Edges \/ <<v, u>> \in Edges
        /\ dist[v] < dist[u]
        /\ /\ mom' = [mom EXCEPT ![u] = IF v = Root THEN Root ELSE mom[v]]
           /\ dist' = [dist EXCEPT ![u] = dist[v] + 1]

Termination ==
    \A u \in Nodes : dist[u] < MaxCardinality

CorrectSpanningTree ==
    \A u \in Nodes \ {Root} :
        /\ \E v \in Nodes : mom[u] = v
        /\ LET path == <<u>> \o ([n \in TLCGetSet(u, mom) |-> mom[n]]).pathTo(Root)
           IN  \A i \in 1..Len(path)-1 : <<path[i], path[i+1]>> \in Edges \/ <<path[i+1], path[i]>> \in Edges

Spec ==
    /\ Init
    /\ [][Next]_<<mom, dist>>
    /\ WF_next(<<mom, dist>>)

Inv == Termination => CorrectSpanningTree

\* Liveness properties
TerminatesEventually == <>[](Termination)
ParentRootEventually == \A u \in Nodes : <>[](mom[u] = Root)

====