---------------------------- MODULE Github648 ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Graph

VARIABLES v, w

BoundedSeq(S, n) == UNION {[1..i -> S] : i \in 0..n}

BoundedSeqTLCEval(S, n) == TLCEval(UNION {[1..i -> S] : i \in 0..n})

ASSUME Cardinality(BoundedSeqTLCEval(BoundedSeqTLCEval({1,2}, 2), 2)) = 57

DirectedGraphs(nodes) == {[edges |-> e] : e \in SUBSET (nodes \times nodes)}

TestGraph == TLCEval([edges |-> RandomElement({g.edges : g \in DirectedGraphs({1,2,3})}) \union {<<1,1>>}])

Init == 
    /\ v \in Graph.edges
    /\ w \in Graph.edges

Next == 
    /\ v' \in Graph.edges
    /\ w' \in Graph.edges

Inv == 
    /\ v \in Graph.edges
    /\ w \in Graph.edges
    /\ v \in TestGraph.edges
    /\ w \in TestGraph.edges
    /\ TLCEval(Cardinality(TLCEval(BoundedSeq(BoundedSeq({1,2,3}, 3), 3)))) = 65641

=============================================================================