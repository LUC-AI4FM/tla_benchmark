---------------------------- MODULE SpanTreeTest ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Root, MaxCardinality

ASSUME /\ Root \in Nodes
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

VARIABLES mom, dist, Edges

vars == <<mom, dist, Edges>>

\* All possible undirected edges (unordered pairs of distinct nodes)
AllEdges == {e \in SUBSET Nodes : Cardinality(e) = 2}

\* Neighbors of node n in the chosen graph
Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

TypeOK ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> Nat]
  /\ Edges \subseteq AllEdges

\* Non-deterministically choose any undirected graph over Nodes
Init ==
  /\ Edges \in SUBSET AllEdges
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

\* A node n adopts a neighbor m as parent if m offers a shorter path
Update(n, m) ==
  /\ dist[m] + 1 < dist[n]
  /\ \E d \in (dist[m] + 1)..(dist[n] - 1) :
        /\ dist' = [dist EXCEPT ![n] = d]
        /\ mom' = [mom EXCEPT ![n] = m]
  /\ UNCHANGED Edges

Next == \E n \in Nodes : \E m \in Nbrs(n) : Update(n, m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

PostCondition ==
  \A n \in Nodes :
    \/ /\ n = Root
       /\ dist[n] = 0
       /\ mom[n] = n
    \/ /\ n # Root
       /\ dist[n] = MaxCardinality
       /\ mom[n] = n
       /\ \A m \in Nbrs(n) : dist[m] = MaxCardinality
    \/ /\ n # Root
       /\ dist[n] \in 1..(MaxCardinality - 1)
       /\ mom[n] \in Nbrs(n)
       /\ dist[n] = dist[mom[n]] + 1

Terminated == ~ ENABLED Next

\* Safety: whenever the algorithm has terminated, the post-condition holds
Safety == [](Terminated => PostCondition)

\* Liveness: the post-condition is eventually reached
Liveness == <>PostCondition

\* Termination: under fair scheduling the computation terminates
Termination == <>Terminated

THEOREM Spec => []TypeOK
THEOREM Spec => Safety
THEOREM Spec => Liveness
THEOREM Spec => Termination
=============================================================================