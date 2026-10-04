---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root, MaxDist

ASSUME Root \in Nodes
ASSUME MaxDist >= Cardinality(Nodes)

VARIABLES dist, parent, Edges

vars == <<dist, parent, Edges>>

-----------------------------------------------------------------------------

(* Generate a random symmetric edge relation for an undirected graph *)
RandomEdges == 
    LET AllPairs == {<<n, m>> : n \in Nodes, m \in Nodes \ {n}}
    IN {<<n, m>> \in AllPairs : RandomElement({TRUE, FALSE})}

SymmetricClosure(E) ==
    E \cup {<<m, n>> : <<n, m>> \in E}

Neighbors(n) == {m \in Nodes : <<n, m>> \in Edges}

-----------------------------------------------------------------------------

Init ==
    /\ Edges = SymmetricClosure(RandomEdges)
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDist]
    /\ parent = [n \in Nodes |-> n]

-----------------------------------------------------------------------------

(* A node n can improve by adopting neighbor m as parent if:
   - m is a neighbor of n
   - m's distance is strictly less than n's distance minus 1
   - The new distance (m's distance + 1) is strictly between m's distance + 1 and n's current distance
   This simplifies to: dist[m] + 1 < dist[n] *)
   
CanImprove(n, m) ==
    /\ m \in Neighbors(n)
    /\ dist[m] + 1 < dist[n]

Improve(n, m) ==
    /\ CanImprove(n, m)
    /\ dist' = [dist EXCEPT ![n] = dist[m] + 1]
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ Edges' = Edges

Next ==
    \E n \in Nodes : \E m \in Nodes : Improve(n, m)

Stutter ==
    UNCHANGED vars

Fairness ==
    WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

(* Type invariant *)
TypeOK ==
    /\ dist \in [Nodes -> 0..MaxDist]
    /\ parent \in [Nodes -> Nodes]
    /\ Edges \subseteq (Nodes \X Nodes)
    /\ \A <<n, m>> \in Edges : <<m, n>> \in Edges  \* Symmetric

-----------------------------------------------------------------------------

(* Quiescence: no improvement is possible *)
Quiescent ==
    ~\E n \in Nodes : \E m \in Nodes : CanImprove(n, m)

(* Reachability from root in the graph *)
RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
    LET NewNodes == S \cup UNION {Neighbors(n) : n \in S}
    IN IF NewNodes = S THEN S ELSE ReachableFrom(NewNodes)

ReachableNodes == ReachableFrom({Root})

(* A node is in the spanning tree if it can trace back to root via parent pointers *)
RECURSIVE TracesToRoot(_,_)
TracesToRoot(n, visited) ==
    IF n = Root THEN TRUE
    ELSE IF n \in visited THEN FALSE
    ELSE IF parent[n] = n THEN FALSE
    ELSE TracesToRoot(parent[n], visited \cup {n})

InSpanningTree(n) == TracesToRoot(n, {})

(* Safety: when quiescent, the result forms a valid spanning tree for reachable nodes
   and correctly identifies unreachable nodes *)
Safety ==
    Quiescent =>
        /\ \A n \in ReachableNodes \ {Root} :
            /\ dist[n] = dist[parent[n]] + 1
            /\ parent[n] \in Neighbors(n)
            /\ InSpanningTree(n)
        /\ dist[Root] = 0
        /\ parent[Root] = Root
        /\ \A n \in Nodes \ ReachableNodes :
            /\ dist[n] = MaxDist
            /\ parent[n] = n

(* Liveness: the algorithm eventually reaches quiescence *)
Liveness == <>Quiescent

=============================================================================