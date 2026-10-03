---------------------------- MODULE BoundedSequencesAndGraphs ----------------------------
EXTENDS Integers, TLC

CONSTANT Graph

VARIABLE x, y

x == RandomElement(Graph.edges)
y == RandomElement(Graph.edges)

Init ==
  /\ x \in Graph.edges
  /\ y \in Graph.edges

Next ==
  /\ x' = RandomElement(Graph.edges)
  /\ y' = RandomElement(Graph.edges)

Inv ==
  /\ x \in TestGraph.edges
  /\ y \in TestGraph.edges
  /\ TLCEval(Cardinality(Sequences(2, Graph.edges))) = 10

TestGraph == [ edges <- Graph.edges ]

=============================================================================