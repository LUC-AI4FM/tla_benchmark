---------------------------- MODULE specification ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Graph

\* Helper operator for bounded sequences up to length n
BoundedSeq(S, n) == UNION {[1..m -> S] : m \in 0..n}

\* Helper operator to get the set of edges from a directed graph representation
\* Assumes Graph is a set of edges represented as <<from, to>> tuples
Edges(G) == G

\* Get the set of nodes from a graph (edges are <<from, to>> pairs)
Nodes(G) == {e[1] : e \in G} \cup {e[2] : e \in G}

\* Assumption about cardinality of a nested bounded-sequence construction
\* This exercises TLC's evaluation of complex set expressions
ASSUME Cardinality(BoundedSeq(BoundedSeq({1, 2}, 2), 2)) >= 1

\* TestGraph is derived from Graph using TLCEval to force evaluation
\* The caching behavior of TLCEval matters for correctness of the invariant
TestGraph == TLCEval(Graph)

VARIABLES x, y

vars == <<x, y>>

\* Type invariant: x and y must be edges in the Graph
TypeOK == /\ x \in Edges(Graph)
          /\ y \in Edges(Graph)

\* Initial state: both variables are random elements from the edge set
\* RandomElement forces TLC to pick non-deterministically for simulation
Init == /\ x \in Edges(Graph)
        /\ y \in Edges(Graph)

\* Next state: either x or y transitions to another edge in the graph
\* Using TLCEval to force evaluation context for caching behavior
Next == \/ /\ x' \in Edges(TLCEval(Graph))
           /\ y' = y
        \/ /\ y' \in Edges(TLCEval(Graph))
           /\ x' = x

\* The invariant asserts:
\* 1. Type membership of the variables (x and y are edges)
\* 2. Membership in the derived TestGraph
\* 3. A fixed TLCEval-computed cardinality check
\* The caching behavior matters: TLCEval should return consistent results
Inv == /\ TypeOK
       /\ x \in Edges(TestGraph)
       /\ y \in Edges(TestGraph)
       /\ TLCEval(Cardinality(Edges(Graph))) = Cardinality(Edges(TestGraph))

=============================================================================