---- MODULE BoundedSeqGraph ----
EXTENDS TLC, Randomization, Sequences, FiniteSets, Integers

VARIABLES
  x,
  y

\* Helper operator for bounded sequences.
BSeq(S, N) == [1..N -> S]

\* Helper operator to get the set of nodes from a graph.
Nodes(G) == UNION { {v[1], v[2]} : v \in G }

\* A constant graph, defined as a set of edges (pairs).
Graph == {<<1,2>>, <<2,1>>, <<2,3>>, <<3,2>>, <<3,1>>, <<1,3>>}

\* A derived graph, containing a subset of edges from the main Graph.
TestGraph == {e \in Graph : e[1] < e[2]}

\* An assumption about the cardinality of a nested sequence construction.
\* For the defined Graph, Nodes(Graph) = {1,2,3}, so its cardinality is 3.
\* The cardinality of BSeq(Nodes(Graph), 2) is 3^2 = 9.
\* The cardinality of the nested BSeq below is thus 9^2 = 81.
ASSUME Cardinality(BSeq(BSeq(Nodes(Graph), 2), 2)) = 81

\* Initial state predicate. Variables are initialized to any edge in the graph.
Init ==
  /\ x \in Graph
  /\ y \in Graph

\* Next-state relation. In each step, variables are assigned a new random edge.
Next ==
  /\ x' = RandomElement(Graph)
  /\ y' = RandomElement(Graph)

\* The invariant asserts type membership and a property on the variables.
\* It also includes a check on a constant expression using TLCEval.
\* The use of TLCEval forces TLC to evaluate the expression in the current
\* context. This is relevant when TLC's caching of constant expressions
\* might otherwise obscure behavior, although for this specific constant
\* expression, it primarily serves as a demonstration of the operator.
Inv ==
  /\ x \in TestGraph
  /\ y \in TestGraph
  /\ TLCEval(Cardinality(BSeq(BSeq(Nodes(Graph), 2), 2))) = 81

=============================================================================