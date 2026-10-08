---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, Bound

VARIABLES parent, dist, msgs

vars == <<parent, dist, msgs>>

\* Helper: get the set of neighbors for a node
Neighbors(n) == {m \in Nodes : {n, m} \in Edges \/ {m, n} \in Edges}

\* Check if a node is reachable from Root in the graph
ReachableFrom[s \in SUBSET Nodes] ==
    LET Extend(S) == S \cup UNION {{m \in Nodes : {n, m} \in Edges \/ {m, n} \in Edges} : n \in S}
    IN  LET RECURSIVE Closure(_)
            Closure(S) == IF Extend(S) = S THEN S ELSE Closure(Extend(S))
        IN Closure(s)

Reachable == ReachableFrom[{Root}]

\* Type invariant
TypeOK ==
    /\ parent \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..Bound]
    /\ msgs \subseteq (Nodes \times Nodes \times (0..Bound))

\* Initial state
Init ==
    /\ parent = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Bound]
    /\ msgs = {<<Root, m, 0>> : m \in Neighbors(Root)}

\* A node n receives a message from neighbor m with distance d
ReceiveMessage(n, m, d) ==
    /\ <<m, n, d>> \in msgs
    /\ msgs' = msgs \ {<<m, n, d>>}
    /\ IF d + 1 < dist[n]
       THEN /\ dist' = [dist EXCEPT ![n] = d + 1]
            /\ parent' = [parent EXCEPT ![n] = m]
            /\ msgs' = (msgs \ {<<m, n, d>>}) \cup 
                       {<<n, nbr, d + 1>> : nbr \in Neighbors(n)}
       ELSE /\ dist' = dist
            /\ parent' = parent

\* Next state relation: some node processes some message
Next ==
    \E n \in Nodes : \E m \in Nodes : \E d \in 0..Bound :
        /\ <<m, n, d>> \in msgs
        /\ IF d + 1 < dist[n]
           THEN /\ dist' = [dist EXCEPT ![n] = d + 1]
                /\ parent' = [parent EXCEPT ![n] = m]
                /\ msgs' = (msgs \ {<<m, n, d>>}) \cup 
                           {<<n, nbr, d + 1>> : nbr \in Neighbors(n)}
           ELSE /\ dist' = dist
                /\ parent' = parent
                /\ msgs' = msgs \ {<<m, n, d>>}

\* Quiescence: no messages pending
Quiescent == msgs = {}

\* Spanning tree correctness when quiescent:
\* - For reachable nodes: parent points to a neighbor, and following parents reaches Root
\* - For unreachable nodes: parent points to self
\* - Distance equals hop distance from Root (or Bound for unreachable)

\* Check if following parent from n reaches Root within Bound steps
ReachesRoot[n \in Nodes] ==
    LET RECURSIVE Follow(_, _)
        Follow(node, steps) ==
            IF node = Root THEN TRUE
            ELSE IF steps = 0 THEN FALSE
            ELSE IF parent[node] = node THEN FALSE
            ELSE Follow(parent[node], steps - 1)
    IN Follow(n, Bound)

\* The post-condition that must hold upon quiescence
PostCondition ==
    /\ \A n \in Reachable :
        /\ dist[n] < Bound
        /\ (n = Root => parent[n] = n /\ dist[n] = 0)
        /\ (n # Root => 
            /\ parent[n] \in Neighbors(n)
            /\ dist[n] = dist[parent[n]] + 1
            /\ ReachesRoot[n])
    /\ \A n \in Nodes \ Reachable :
        /\ parent[n] = n
        /\ dist[n] = Bound

\* Safety: if quiescent, the post-condition holds
Safety == Quiescent => PostCondition

\* Liveness: the system eventually quiesces and the post-condition holds
Liveness == <>(Quiescent /\ PostCondition)

\* Fair specification
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================