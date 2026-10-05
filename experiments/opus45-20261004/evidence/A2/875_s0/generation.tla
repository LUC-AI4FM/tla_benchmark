---------------------------- MODULE SpanningTreeRandom ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root, MaxCardinality

ASSUME Root \in Nodes
ASSUME MaxCardinality \in Nat /\ MaxCardinality >= Cardinality(Nodes)

\* Generate random undirected edges
EdgesFrom(n) == RandomElement(SUBSET (Nodes \ {n}))
GeneratedEdges == UNION {{n, m} : n \in Nodes, m \in EdgesFrom(n)}
Edges == {{n, m} \in GeneratedEdges : n # m}

\* Neighbors of a node in the undirected graph
Neighbors(n) == {m \in Nodes : {n, m} \in Edges}

VARIABLES mom, dist

vars == <<mom, dist>>

TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..MaxCardinality]

Init ==
    /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

\* A node n can update if it has a neighbor m with dist[m] < dist[n] - 1
CanUpdate(n, m) ==
    /\ m \in Neighbors(n)
    /\ dist[m] < dist[n] - 1

Update(n, m) ==
    /\ CanUpdate(n, m)
    /\ \E d \in (dist[m] + 1)..(dist[n] - 1) :
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ mom' = [mom EXCEPT ![n] = m]

Next ==
    \E n \in Nodes : \E m \in Nodes :
        Update(n, m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Post-condition for termination
PostCondition ==
    \A n \in Nodes :
        \/ (n = Root /\ dist[n] = 0)
        \/ (dist[n] = MaxCardinality /\ \A m \in Neighbors(n) : dist[m] = MaxCardinality)
        \/ (dist[n] = dist[mom[n]] + 1 /\ mom[n] \in Neighbors(n))

\* No further steps are enabled
Termination == ~ENABLED Next

\* Safety: when terminated, post-condition holds
Safety == Termination => PostCondition

\* Liveness: post-condition is eventually reached
Liveness == <>PostCondition

===============================================================================