---- MODULE SpanningTree ----
EXTENDS Integers, FiniteSets, TLC

CONSTANT Nodes, Root
ASSUME IsFiniteSet(Nodes) ∧ (Root ∈ Nodes)

Infinity == Cardinality(Nodes)

AllPossibleEdges == { {n, m} \in SUBSET Nodes : Cardinality({n, m}) = 2 }

\* Edges is a randomly chosen set of undirected edges.
Edges == RandomElement(SUBSET AllPossibleEdges)

\* The set of neighbors for a given node.
Neighbors(n \in Nodes) == {m \in Nodes : {n, m} \in Edges}

VARIABLES mom, dist
vars == <<mom, dist>>

TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..Infinity]

Init ==
    /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]

Next ==
    \/ ∃ n \in Nodes :
        ∃ m \in Neighbors(n) :
            \* A node n can adopt a neighbor m if m's distance is strictly
            \* smaller and there exists an intermediate distance value to choose.
            dist[n] > dist[m] + 1
            /\ ∃ d \in (dist[m] + 1)..(dist[n] - 1) :
                /\ mom' = [mom EXCEPT ![n] = m]
                /\ dist' = [dist EXCEPT ![n] = d]

Postcondition ==
    LET Reachable   == {n \in Nodes : dist[n] < Infinity}
        Unreachable == {n \in Nodes : dist[n] = Infinity}
    IN
    \* The root is correctly configured.
    /\ mom[Root] = Root
    /\ dist[Root] = 0

    \* Every reachable non-root node points to a neighbor with a smaller distance.
    /\ ∀ n \in Reachable \ {Root} :
        /\ mom[n] \in Neighbors(n)
        /\ dist[n] > dist[mom[n]]

    \* Every unreachable node points to itself.
    /\ ∀ n \in Unreachable :
        mom[n] = n

    \* The set of unreachable nodes is closed under the neighbor relation
    \* (i.e., no unreachable node has a reachable neighbor).
    /\ ∀ n \in Unreachable :
        ∀ m \in Neighbors(n) :
            m \in Unreachable

Spec == Init ∧ □[Next]_vars ∧ WF_vars(Next)

Safety == □(¬ENABLED Next ⇒ Postcondition)

Liveness == ◇Postcondition

=============================================================================