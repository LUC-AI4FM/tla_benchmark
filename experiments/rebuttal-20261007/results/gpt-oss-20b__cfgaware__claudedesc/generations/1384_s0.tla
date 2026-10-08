------------------------------ MODULE Github648 ------------------------------
EXTENDS Sequences, FiniteSets

CONSTANTS Graph

(* Utility operators *)

BoundedSeq(S, n) == { seq \in Seq(S) : Len(seq) <= n }

BoundedSeqTLCEval(S, n) == TLCEval(BoundedSeq(S, n))

DirectedGraphs(nodes) ==
    { [ edges |-> E ] : E \subseteq nodes \times nodes }

RandomElement(S) == CHOOSE x \in S : TRUE

TestGraph ==
    TLCEval(
        [ edges |-> (RandomElement(DirectedGraphs({1,2,3})).edges \cup {<<1,1>>}) ]
    )

THEOREM BoundedSeqCardinality ==
    Cardinality(BoundedSeqTLCEval(BoundedSeqTLCEval({1,2}, 2), 2)) = 57

VARIABLES v, w

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
    /\ Cardinality(BoundedSeqTLCEval(
            BoundedSeqTLCEval({1,2,3}, 3), 3)) = 65641

===============================================================================