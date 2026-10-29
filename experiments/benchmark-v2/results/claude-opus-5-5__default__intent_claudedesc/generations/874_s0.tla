------------------------------ MODULE SpanningTree ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, Root

ASSUME RootInNodes == Root \in Nodes
ASSUME EdgesWellFormed ==
          \A e \in Edges : /\ e \subseteq Nodes
                           /\ Cardinality(e) = 2

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

\* Nodes reachable from Root within k hops in the graph
RECURSIVE ReachIn(_)
ReachIn(k) == IF k = 0 THEN {Root}
              ELSE LET R == ReachIn(k - 1)
                   IN  R \cup UNION {Nbrs(x) : x \in R}

N == Cardinality(Nodes)

\* The graph is connected: every node is reachable from the root
ASSUME Connected == ReachIn(N) = Nodes

\* Value used as "infinite" distance; strictly larger than any real distance
Infinity == N

\* True graph distance from Root
Distance(n) == CHOOSE k \in 0..N : /\ n \in ReachIn(k)
                                   /\ \A j \in 0..(k - 1) : n \notin ReachIn(j)

VARIABLES mom, dist
vars == <<mom, dist>>

TypeOK == /\ mom  \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> 0..Infinity]

Init == /\ mom  = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]

\* Node n learns from neighbor m a shorter route to the root
Update(n, m) ==
    /\ m \in Nbrs(n)
    /\ dist[m] + 1 < dist[n]
    /\ \E d \in (dist[m] + 1)..(dist[n] - 1) :
          /\ dist' = [dist EXCEPT ![n] = d]
          /\ mom'  = [mom  EXCEPT ![n] = m]

Next == \E n \in Nodes : \E m \in Nbrs(n) : Update(n, m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Iterated parent function
RECURSIVE MomPow(_, _)
MomPow(n, k) == IF k = 0 THEN n ELSE mom[MomPow(n, k - 1)]

\* Safety invariants (hold in every reachable state)

RootProperty == /\ mom[Root] = Root
                /\ dist[Root] = 0

ParentIsNeighbor ==
    \A n \in Nodes \ {Root} : mom[n] # n => mom[n] \in Nbrs(n)

\* A node's parent is strictly closer to the root (ensures no cycles)
ParentCloser ==
    \A n \in Nodes \ {Root} : mom[n] # n => dist[mom[n]] < dist[n]

\* Assigned distances never undercut the true graph distance
DistanceSound ==
    \A n \in Nodes : dist[n] >= Distance(n)

\* Nodes with no parent yet have infinite distance
UnassignedInfinite ==
    \A n \in Nodes \ {Root} : (mom[n] = n) <=> (dist[n] = Infinity)

NoCycles ==
    \A n \in Nodes \ {Root} :
        mom[n] # n => \A k \in 1..N : MomPow(n, k) # n

Inv == /\ TypeOK
       /\ RootProperty
       /\ ParentIsNeighbor
       /\ ParentCloser
       /\ DistanceSound
       /\ UnassignedInfinite
       /\ NoCycles

-----------------------------------------------------------------------------
\* Final, complete spanning tree

ValidParents ==
    \A n \in Nodes \ {Root} : mom[n] \in Nbrs(n)

DistanceConsistency ==
    \A n \in Nodes :
        IF n = Root THEN dist[n] = 0
                    ELSE dist[n] = dist[mom[n]] + 1

TreeStructure ==
    \A n \in Nodes : \E k \in 0..N : MomPow(n, k) = Root

CorrectDistances ==
    \A n \in Nodes : dist[n] = Distance(n)

PostCondition == /\ RootProperty
                 /\ ValidParents
                 /\ DistanceConsistency
                 /\ TreeStructure
                 /\ CorrectDistances

\* Liveness: the algorithm eventually stabilizes on a complete spanning tree
Termination == <>[](PostCondition /\ ~ENABLED Next)

EventuallyParent ==
    \A n \in Nodes \ {Root} : <>[](mom[n] \in Nbrs(n))

THEOREM Spec => []Inv
THEOREM Spec => Termination
=============================================================================