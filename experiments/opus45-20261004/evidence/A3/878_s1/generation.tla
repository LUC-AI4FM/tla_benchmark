---------------------------- MODULE RootedSpanningTree ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME Root \in Nodes
ASSUME MaxCardinality \in Nat
ASSUME MaxCardinality >= Cardinality(Nodes)

Neighbors(n) == {m \in Nodes : {n, m} \in Edges \/ {m, n} \in Edges}

VARIABLES mom, dist

vars == <<mom, dist>>

TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..MaxCardinality]

Init ==
    /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Update(n, m, d) ==
    /\ m \in Neighbors(n)
    /\ dist[m] < dist[n]
    /\ d > dist[m]
    /\ d < dist[n]
    /\ mom' = [mom EXCEPT ![n] = m]
    /\ dist' = [dist EXCEPT ![n] = d]

Next ==
    \E n \in Nodes : \E m \in Nodes : \E d \in 0..MaxCardinality :
        Update(n, m, d)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Terminated ==
    ~ENABLED Next

ReachableFromRoot ==
    LET RECURSIVE Reachable(_)
        Reachable(S) ==
            LET NewNodes == {n \in Nodes : \E m \in S : n \in Neighbors(m)}
            IN IF NewNodes \ S = {} THEN S
               ELSE Reachable(S \cup NewNodes)
    IN Reachable({Root})

IsTree ==
    /\ mom[Root] = Root
    /\ \A n \in Nodes \ {Root} : 
        /\ mom[n] \in Neighbors(n)
        /\ dist[n] = dist[mom[n]] + 1

Postcondition ==
    /\ \A n \in ReachableFromRoot : dist[n] < MaxCardinality
    /\ \A n \in Nodes \ ReachableFromRoot : dist[n] = MaxCardinality
    /\ \A n \in ReachableFromRoot \ {Root} : mom[n] \in Neighbors(n)
    /\ \A n \in ReachableFromRoot \ {Root} : dist[n] > dist[mom[n]]
    /\ mom[Root] = Root
    /\ dist[Root] = 0

Safety == Terminated => Postcondition

Liveness == <>Terminated

EventuallyRootParent == \A n \in Nodes : <>(mom[n] = Root)

===============================================================================