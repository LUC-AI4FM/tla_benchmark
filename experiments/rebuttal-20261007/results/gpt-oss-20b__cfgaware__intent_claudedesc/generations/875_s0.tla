------------------------------ MODULE SpanningTree ------------------------------
EXTENDS Naturals, TLC

CONSTANTS Nodes, Root, Adj, MaxDist

(* Type constraints *)
TypeOK == 
    /\ dist \in [Nodes -> Nat]
    /\ parent \in [Nodes -> Nodes]

VARIABLES dist, parent

Init ==
    /\ dist = [i \in Nodes |-> IF i = Root THEN 0 ELSE MaxDist]
    /\ parent = [i \in Nodes |-> i]

Quiescent == 
    \A i \in Nodes : \A j \in Adj[i] : dist[j] + 1 >= dist[i]

Update ==
    \E i \in Nodes :
        \E j \in Adj[i] :
            /\ dist[j] + 1 < dist[i]
            /\ parent' = [parent EXCEPT ![i] = j]
            /\ dist'   = [dist EXCEPT ![i] = dist[j] + 1]

Stutter ==
    /\ dist' = dist
    /\ parent' = parent

Next == Update \/ Stutter

Spec == Init /\ [] (Next)_<<dist, parent>>

Safety ==
    \A i \in Nodes :
        IF i = Root THEN
            /\ parent[i] = i
            /\ dist[i] = 0
        ELSEIF dist[i] < MaxDist THEN
            /\ parent[i] \in Adj[i]
            /\ dist[parent[i]] + 1 = dist[i]
        ELSE
            /\ parent[i] = i
            /\ (\A j \in Adj[i] : dist[j] >= MaxDist)

Liveness == <> Quiescent

=============================================================================