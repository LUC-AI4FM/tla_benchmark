----------------------------- MODULE RandomizedSpanningTree -----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root

VARIABLES mom, dist

Edges == [n \in Nodes |-> RANDOM_SUBSET(Nodes \ {n})]

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE \infinity]

Next ==
    LET n \in Nodes
        newMom \in Edges[n] 
        newDist \in (dist[newMom] + 1) ..below dist[n]
    IN \/ /\ newMom \in mom[n]
         /\ dist[mom[n]] < dist[n]
      \/ /\ newMom \notin mom[n]
         /\ dist[newMom] < dist[n]
         /\ UNCHANGED <<mom EXCEPT ![n] = newMom>>, dist EXCEPT ![n] = newDist

RootedSpanningTree ==
    /\ \A n \in Nodes : (dist[n] = \infinity) \/ (mom[n] \in Edges[n])
    /\ \A n \in Nodes \ {Root} : \E path \in SUBSET Nodes :
            /\ Root \notin path
            /\ n \in path
            /\ mom[n] \in path
            /\ \A m \in path : dist[mom[m]] < dist[m]
            /\ dist[CHOOSE m \in path : mom[m] = Root] = 0

Safety == [](RootedSpanningTree \/ (\A n \in Nodes : dist[n] = \infinity))

Liveness == <>(\A n \in Nodes : (dist[n] = \infinity) \/ (mom[n] \in Edges[n]))

Spec ==
    /\ Init
    /\ [][Next]_<<mom, dist>>
    /\ WF_vars(Next)
    /\ Safety
    /\ Liveness

================================================================================