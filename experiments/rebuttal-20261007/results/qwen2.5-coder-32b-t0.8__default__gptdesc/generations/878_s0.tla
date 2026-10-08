------------------------------- MODULE SpanningTree -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Root, MaxCardinality
ASSUME Root \in Nodes
ASSUME MaxCardinality > 0
ASSUME \A n \in Nodes : NodeIsConnected(n)

VARIABLES mom, dist

Init == /\ mom = [n \in Nodes |-> n]
      /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next ==
    \/ \E u \in Nodes :
        \E v \in Nodes :
            \E newDist \in 1..(dist[v] - 1) :
                /\ mom' = [mom EXCEPT ![u] = v]
                /\ dist' = [dist EXCEPT ![u] = newDist]
    \/ UNCHANGED mom
       /\ UNCHANGED dist

Safety == 
    /\ \A u \in Nodes : (dist[u] = 0 => u = Root)
    /\ \A u \in Nodes \ {Root} : \E! v \in Nodes : mom[v] = u

Termination ==
    /\ \A u \in Nodes : dist[u] /= MaxCardinality
    /\ \A u \in Nodes : (u = Root => dist[u] = 0)
    /\ \A u \in Nodes \ {Root} : (dist[mom[u]] < dist[u])
    /\ Acyclic(mom, Root)

Acyclic(m, r) ==
    LET Path(n) == {n} \cup {m[n]} \cup Path(m[n])
    IN  \A n \in Nodes \ {r} : n \notin Path(m[n])

Liveness ==
    <>[](\A u \in Nodes : mom[u] = Root)

Spec ==
    /\ Init
    /\ [][Next]_<<mom, dist>>
    /\ WF_next(Next)
    /\ Safety
    /\ Termination => Liveness

=============================================================================