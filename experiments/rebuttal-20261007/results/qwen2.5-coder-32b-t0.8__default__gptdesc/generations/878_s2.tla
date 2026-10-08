------------------------------- MODULE SpanningTree -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Root, MaxCardinality

VARIABLES mom, dist

Init == /\ mom \in [Nodes -> Nodes]
        /\ dist \in [Nodes -> 0..MaxCardinality]
        /\ \A n \in Nodes: mom[n] = n
        /\ dist[Root] = 0
        /\ \A n \in Nodes \ {Root}: dist[n] = MaxCardinality

Next == \E u, v \in Nodes:
          /\ u # Root
          /\ v \in Neighbors[u]
          /\ dist[v] < dist[u]
          /\ \E d \in (dist[v]+1)..(dist[u]-1):
               \/ /\ mom' = [mom EXCEPT ![u] = v]
                  /\ dist' = [dist EXCEPT ![u] = d]

Safety == [](dist[Root] = 0) /\
            [](FORALL u, v \in Nodes: v \notin Neighbors[u] \/ mom[v] # u) /\
            [](FORALL u \in Nodes \ {Root}: mom[u] \in Neighbors[u]) /\
            [](FORALL u \in Nodes \ {Root}: dist[u] > 0)

Termination == <>(FORALL u \in Nodes: dist[u] >= dist[mom[u]] \/ mom[u] = Root)

Postcondition == (\E r \in Nodes:
                    /\ mom[r] = r
                    /\ FORALL u \in Nodes \ {r}: mom[u] \in Neighbors[u]
                    /\ dist[u] > 0
                    /\ dist[u] >= dist[mom[u]]
                    /\ (FORALL v \in Nodes: Reachable(r, v) => dist[v] < MaxCardinality))

Reachable(u, v) == \/ u = v
                     \/ \E w \in Nodes: mom[w] = u /\ Reachable(w, v)

Spec == Init /\ [][Next]_<<mom, dist>> /\ WF_next(Next)

THEOREM Spec => []Safety
THEOREM Spec => <>Termination
THEOREM Spec => <>Postcondition
===============================================================================