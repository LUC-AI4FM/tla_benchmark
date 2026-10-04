---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxNodes

ASSUME Root \in Nodes
ASSUME \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2
ASSUME MaxNodes \in Nat /\ MaxNodes >= Cardinality(Nodes)

VARIABLES dist, parent

vars == <<dist, parent>>

Neighbors(n) == {m \in Nodes : {n, m} \in Edges}

Init ==
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxNodes]
    /\ parent = [n \in Nodes |-> n]

CanImprove(n, m) ==
    /\ m \in Neighbors(n)
    /\ dist[n] > dist[m] + 1

Improve(n, m, newDist) ==
    /\ CanImprove(n, m)
    /\ newDist > dist[m] + 1
    /\ newDist < dist[n]
    /\ dist' = [dist EXCEPT ![n] = newDist]
    /\ parent' = [parent EXCEPT ![n] = m]

ImproveExact(n, m) ==
    /\ CanImprove(n, m)
    /\ dist' = [dist EXCEPT ![n] = dist[m] + 1]
    /\ parent' = [parent EXCEPT ![n] = m]

Next ==
    \E n \in Nodes : \E m \in Neighbors(n) : ImproveExact(n, m)

Terminated ==
    ~\E n \in Nodes : \E m \in Neighbors(n) : CanImprove(n, m)

Stutter ==
    /\ Terminated
    /\ UNCHANGED vars

NextOrStutter ==
    Next \/ Stutter

Spec == Init /\ [][NextOrStutter]_vars /\ WF_vars(Next)

ReachableFrom(start) ==
    LET RECURSIVE Reach(_)
        Reach(S) ==
            LET New == {m \in Nodes : \E n \in S : m \in Neighbors(n)} \ S
            IN IF New = {} THEN S ELSE Reach(S \cup New)
    IN Reach({start})

Reachable == ReachableFrom(Root)

RootCorrect ==
    Terminated => (dist[Root] = 0 /\ parent[Root] = Root)

UnreachableCorrect ==
    Terminated =>
        \A n \in Nodes \ Reachable :
            /\ dist[n] = MaxNodes
            /\ parent[n] = n
            /\ \A m \in Neighbors(n) : dist[m] >= dist[n]

ReachableCorrect ==
    Terminated =>
        \A n \in Reachable \ {Root} :
            /\ dist[n] = dist[parent[n]] + 1
            /\ parent[n] \in Neighbors(n)

SafetyInvariant ==
    /\ RootCorrect
    /\ UnreachableCorrect
    /\ ReachableCorrect

DistNonNegative ==
    \A n \in Nodes : dist[n] >= 0 /\ dist[n] <= MaxNodes

ParentValid ==
    \A n \in Nodes : parent[n] \in Nodes

TypeInvariant ==
    /\ DistNonNegative
    /\ ParentValid

Termination == <>Terminated

=============================================================================