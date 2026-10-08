MODULE RandomSpanningTree
EXTENDS TLC, Integers

CONSTANTS Nodes, Root
ASSUME NodeSetDef == Nodes /= {}
ASSUME RootInNodes == Root \in Nodes

VARIABLES mom, dist, Edges

(* Type Invariant *)
TypeInv ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> Nat]
    /\ Edges \in [Nodes -> SUBSET Nodes]
    /\ \A n \in Nodes : Edges[n] \subseteq Nodes \ {n}

(* Initial state *)
Init ==
    /\ Edges == [n \in Nodes -> RandomSubset(Nodes \ {n})]
    /\ mom == [n \in Nodes -> n]
    /\ dist == [n \in Nodes -> IF n = Root THEN 0 ELSE 1]

(* Next action: a node adopts a neighbor with strictly smaller distance *)
Next ==
    \E i \in Nodes :
        \E j \in Edges[i] :
            dist[j] < dist[i] /\
            LET newDist == ((dist[j] + dist[i]) DIV 2) IN
                /\ mom' = [mom EXCEPT ![i] = j]
                /\ dist' = [dist EXCEPT ![i] = newDist]
                /\ \A k \in Nodes \ {i} :
                    mom'[k] = mom[k] /\ dist'[k] = dist[k]

(* Quiescence predicate *)
Stable ==
    \A n \in Nodes : \A m \in Edges[n] : dist[m] >= dist[n]

(* Postcondition: rooted spanning tree or unreachable nodes *)
PostCond ==
    /\ mom[Root] = Root
    /\ dist[Root] = 0
    /\ \A n \in Nodes :
            IF mom[n] = n THEN
                (n = Root \/ dist[n] > 0)
            ELSE
                dist[mom[n]] < dist[n]

(* Specification *)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Safety ==
    Spec => [] (Stable -> PostCond)

THEOREM Liveness ==
    Spec => <> PostCond

END RandomSpanningTree