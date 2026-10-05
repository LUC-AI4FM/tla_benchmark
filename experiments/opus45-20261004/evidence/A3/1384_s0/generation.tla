---------------------------- MODULE BoundedSeqGraph ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

\* Helper operator for bounded sequences up to length n
BoundedSeq(S, n) == UNION {[1..m -> S] : m \in 0..n}

\* Helper operators for directed graphs
CONSTANT Nodes

\* Edge set of a directed graph (all possible edges)
EdgeSet(N) == N \times N

\* A graph is a set of edges (subset of EdgeSet)
IsGraph(G, N) == G \subseteq EdgeSet(N)

\* Outgoing edges from a node
OutEdges(G, n) == {e \in G : e[1] = n}

\* Successor nodes
Successors(G, n) == {e[2] : e \in OutEdges(G, n)}

\* The constant graph we work with
CONSTANT Graph

\* Assumption about the graph
ASSUME IsGraph(Graph, Nodes)

\* Assumption about cardinality of nested bounded-sequence construction
\* This tests that TLCEval caching works correctly for complex expressions
ASSUME Cardinality(BoundedSeq(BoundedSeq(Nodes, 2), 3)) >= 0

VARIABLES x, y

vars == <<x, y>>

\* Derived test graph - a subgraph based on some condition
\* Using TLCEval to force evaluation in a particular context
TestGraph == TLCEval({e \in Graph : e[1] # e[2]})

\* Type invariant for the variables
TypeOK == /\ x \in EdgeSet(Nodes)
          /\ y \in EdgeSet(Nodes)

\* Membership in the derived test graph
\* The caching behavior of TLCEval matters here - if TestGraph is
\* not cached properly, this could evaluate differently in different contexts
MembershipInv == /\ x \in Graph
                 /\ y \in Graph

\* Fixed TLCEval-computed cardinality check
\* This verifies that the cardinality computation is stable
CardinalityCheck == TLCEval(Cardinality(TestGraph)) = Cardinality(TestGraph)

\* Combined invariant
Invariant == /\ TypeOK
             /\ MembershipInv
             /\ CardinalityCheck

\* Initial state - pick edges from the graph
\* Using RandomElement to demonstrate TLC-specific evaluation
Init == /\ x = IF Graph # {} 
           THEN RandomElement(Graph)
           ELSE <<1, 1>>
        /\ y = IF Graph # {}
           THEN RandomElement(Graph)
           ELSE <<1, 1>>

\* Next state - transition along graph edges
\* We stay within the edge set of the constant graph
Next == \/ /\ Graph # {}
           /\ x' = RandomElement(Graph)
           /\ y' = RandomElement(Graph)
        \/ /\ x' = x
           /\ y' = y

\* Specification with weak fairness
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Liveness property - if graph is non-empty, we eventually visit different edges
Liveness == Graph # {} => <>(x # y)

================================================================================