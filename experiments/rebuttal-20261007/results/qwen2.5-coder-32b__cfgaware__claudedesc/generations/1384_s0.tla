------------------------------- MODULE Github648 -------------------------------

CONSTANTS nodes

VARIABLES v, w

(*--algorithm Github648

variables v \in {}, w \in {};

begin
    Init:
        with Graph <- TestGraph do
            /\ v \in Graph.edges
            /\ w \in Graph.edges;

    Next ==
        \E e1 \in Graph.edges : \E e2 \in Graph.edges :
            \/ /\ v' = e1
               /\ w' = e2

end algorithm;*)

BoundedSeq(S, n) == {seq \in Seq(S) : Len(seq) <= n}

BoundedSeqTLCEval(S, n) == TLCEval(BoundedSeq(S, n))

DirectedGraphs(nodes) ==
    LET NodePairs == [nodes -> nodes]
        Edges == SUBSET NodePairs
    IN  {graph \in [edges: Edges] : TRUE}

TestGraph ==
    LET RandomGraph == CHOOSE g \in DirectedGraphs({1,2,3}) : TRUE
    IN  TLCEval([edges |-> RandomGraph.edges \/ {<<1,1>>}])

Init == 
    /\ v \in Graph.edges
    /\ w \in Graph.edges

Next ==
    \E e1 \in Graph.edges : \E e2 \in Graph.edges :
        \/ /\ v' = e1
           /\ w' = e2

Inv ==
    /\ v \in Graph.edges
    /\ w \in Graph.edges
    /\ TLCEval(Cardinality(BoundedSeqTLCEval(BoundedSeq({1,2}, 3), 3))) = 65641

Graph == TestGraph

ASSUME Cardinality(BoundedSeqTLCEval(BoundedSeqTLCEval({1,2}, 2), 2)) = 57

=============================================================================