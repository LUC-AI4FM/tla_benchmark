------------------------------- MODULE Github648 -------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Graph

VARIABLES v, w

BoundedSeq(S, n) == { s \in Seq(S) : Len(s) <= n }

BoundedSeqTLCEval(S, n) == TLCEval(BoundedSeq(S, n))

DirectedGraphs(nodes) == 
  LET NodePairs == [nodes -> nodes]
  IN  { g \in SUBSET NodePairs : /\ <<x,x>> \in g \forall x \in nodes
                                     /\ \A e \in g: e[1] \in nodes /\ e[2] \in nodes }

TestGraph ==
  LET Graphs == DirectedGraphs({1,2,3})
      SelfLoop == {<<1,1>>}
  IN  TLCEval(CHOOSE g \in Graphs : TRUE) \cup SelfLoop

Init == \/ v = << >> /\ w = << >>
        \/ \E e \in Graph: v = e /\ w = e

Next ==
  \/ \E e \in Graph: v' = e
  \/ \E e \in Graph: w' = e

Inv ==
  /\ v \in Graph
  /\ w \in Graph
  /\ TLCEval(Cardinality(BoundedSeqTLCEval({1,2}, 2))) = 57
  /\ TLCEval(Cardinality(BoundedSeqTLCEval(BoundedSeqTLCEval({1,2,3}, 3), 3))) = 65641

Spec == Init /\ [][Next]_<<v,w>> /\ Inv

=============================================================================