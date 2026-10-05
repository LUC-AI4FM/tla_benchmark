---------------------------- MODULE TLCEvalCaching ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Nodes

VARIABLES edge

\* Bounded sequences: all sequences of length 0 through n over set S
BoundedSeq(S, n) == UNION {[1..i -> S] : i \in 0..n}

\* Directed graphs represented as a set of edges (pairs of nodes)
DirectedGraphs(N) == SUBSET (N \times N)

\* The input graph - all possible edges over Nodes
Graph == Nodes \times Nodes

\* Random selection from directed graphs, wrapped in TLCEval for stable caching
\* TLCEval ensures this is evaluated once and cached, preventing re-evaluation
TestGraph == TLCEval(RandomElement(DirectedGraphs(Nodes)))

\* Verification of context-sensitive caching for bounded sequences
\* BoundedSeq({1,2}, 2) should have 7 elements: 1 empty + 2 length-1 + 4 length-2
\* BoundedSeq(BoundedSeq({1,2}, 2), 2) should have 57 elements
NestedBoundedSeqCard == Cardinality(TLCEval(BoundedSeq(TLCEval(BoundedSeq({1,2}, 2)), 2)))

\* Triple nested case verification
\* This tests deeper nesting of the caching mechanism
TripleNestedBoundedSeqCard == Cardinality(TLCEval(BoundedSeq(TLCEval(BoundedSeq(TLCEval(BoundedSeq({1,2,3}, 3)), 3)), 3)))

\* Mathematical correctness check for nested bounded sequences
CachingCorrectness == 
    /\ NestedBoundedSeqCard = 57
    /\ TripleNestedBoundedSeqCard = 65641

\* Initial state: edge starts as some element from the intersection of Graph and TestGraph
Init == 
    /\ edge \in (Graph \cap TestGraph)

\* Next state: edge transitions to another element in the intersection
Next == 
    /\ edge' \in (Graph \cap TestGraph)

\* Invariant: edge must always be in both Graph and TestGraph
\* This tests stable random element selection - if TestGraph were re-evaluated
\* on each check, it could return different random graphs causing spurious violations
EdgeInvariant == 
    /\ edge \in Graph
    /\ edge \in TestGraph

\* Combined invariant including mathematical correctness and edge stability
Inv == 
    /\ EdgeInvariant
    /\ CachingCorrectness

===============================================================================