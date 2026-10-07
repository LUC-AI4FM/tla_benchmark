------------------------------ MODULE Github648 ------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT Graph

VARIABLES v, w

BoundedSeq(S, n) == { s \in Seq(S) : Len(s) <= n }

BoundedSeqTLCEval(S, n) == TLCEval(BoundedSeq(S, n))

DirectedGraphs(nodes) == { [edges |-> E] : E \in SUBSET (nodes \X nodes) }

TestGraph ==
  LET g == TLCEval(RandomElement(DirectedGraphs({1, 2, 3})))
  IN [edges |-> g.edges \cup {<<1, 1>>}]

ASSUME Cardinality(BoundedSeqTLCEval(BoundedSeqTLCEval({1, 2}, 2), 2)) = 57

Init ==
  /\ v \in Graph.edges
  /\ w \in Graph.edges

Next ==
  /\ v' \in Graph.edges
  /\ w' \in Graph.edges

vars == <<v, w>>

Spec == Init /\ [][Next]_vars

Inv ==
  /\ v \in Graph.edges
  /\ w \in Graph.edges
  /\ v \in TestGraph.edges
  /\ w \in TestGraph.edges
  /\ TLCEval(Cardinality(BoundedSeqTLCEval(TLCEval(BoundedSeqTLCEval({1, 2, 3}, 3)), 3))) = 65641

=============================================================================