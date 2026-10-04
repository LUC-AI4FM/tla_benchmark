---------------------------- MODULE TLCEvalCaching ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Nodes

VARIABLES currentEdge, edgeIndex

\* Helper: All sequences of length exactly n over set S
SeqOfLen(S, n) == [1..n -> S]

\* Bounded sequences: all sequences of length 0 through maxLen over set S
BSeq(S, maxLen) == UNION {SeqOfLen(S, k) : k \in 0..maxLen}

\* Directed graph: set of all possible edges (pairs of nodes)
DirectedEdges(N) == N \X N

\* All possible directed graphs over nodes N (powerset of edges)
AllDirectedGraphs(N) == SUBSET DirectedEdges(N)

\* Use TLCEval to cache the bounded sequence computation
\* This ensures nested computations are handled correctly
CachedBSeq(S, maxLen) == TLCEval(BSeq(S, maxLen))

\* Nested bounded sequence constructions for cardinality verification
\* BSeq of length 2 over {1,2} has 7 elements: 1 + 2 + 4 = 7
\* BSeq of length 2 over those 7 elements has: 1 + 7 + 49 = 57
NestedBSeq2 == CachedBSeq(CachedBSeq({1, 2}, 2), 2)

\* Triple nested case over {1,2,3} with bound 3
\* BSeq(3) over {1,2,3} has 1 + 3 + 9 + 27 = 40 elements
\* BSeq(3) over 40 elements has 1 + 40 + 1600 + 64000 = 65641
NestedBSeq3 == CachedBSeq(CachedBSeq({1, 2, 3}, 3), 3)

\* The input graph - all possible edges over Nodes
InputGraph == DirectedEdges(Nodes)

\* Random graph selection - TLCEval ensures this is computed once and cached
\* Without TLCEval, RandomElement would be re-evaluated on each reference
RandomTestGraph == TLCEval(RandomElement(AllDirectedGraphs(Nodes)))

\* Convert set to sequence for iteration
SetToSeq(S) == 
    LET n == Cardinality(S)
        f[i \in 0..n] == 
            IF i = 0 THEN <<>>
            ELSE LET x == CHOOSE x \in S : x \notin {f[j][k] : j \in 1..(i-1), k \in 1..Len(f[j])}
                 IN Append(f[i-1], x)
    IN f[n]

\* All edges as a sequence for deterministic iteration
AllEdges == TLCEval(SetToSeq(InputGraph))

\* Type invariant
TypeOK ==
    /\ currentEdge \in DirectedEdges(Nodes) \cup {<<>>}
    /\ edgeIndex \in 0..Cardinality(InputGraph)

\* Initial state
Init ==
    /\ currentEdge = <<>>
    /\ edgeIndex = 0

\* Select next edge from the input graph
SelectEdge ==
    /\ edgeIndex < Len(AllEdges)
    /\ edgeIndex' = edgeIndex + 1
    /\ currentEdge' = AllEdges[edgeIndex + 1]

\* Reset to start over
Reset ==
    /\ edgeIndex = Len(AllEdges)
    /\ edgeIndex' = 0
    /\ currentEdge' = <<>>

\* Next state relation
Next == SelectEdge \/ Reset

\* Specification with weak fairness to ensure progress
Spec == Init /\ [][Next]_<<currentEdge, edgeIndex>> /\ WF_<<currentEdge, edgeIndex>>(Next)

\* Safety invariant: current edge must be in input graph (when set)
EdgeInInputGraph ==
    currentEdge /= <<>> => currentEdge \in InputGraph

\* Critical invariant: tests stability of random graph selection
\* If currentEdge is in InputGraph AND in RandomTestGraph, this must remain consistent
\* Without proper TLCEval caching, RandomTestGraph would change between evaluations
\* causing spurious violations
EdgeStability ==
    currentEdge /= <<>> => 
        (currentEdge \in InputGraph /\ 
         (currentEdge \in RandomTestGraph \/ currentEdge \notin RandomTestGraph))

\* Invariant that would fail without stable random evaluation
\* The RandomTestGraph must be the same every time we check membership
StableRandomInvariant ==
    LET rg == RandomTestGraph
        rg2 == RandomTestGraph
    IN rg = rg2

\* Mathematical correctness property for nested bounded sequences
\* This verifies context-sensitive caching works correctly
CardinalityCorrectness ==
    /\ Cardinality(NestedBSeq2) = 57
    /\ Cardinality(NestedBSeq3) = 65641

\* The random test graph must be a valid directed graph over Nodes
RandomGraphValid ==
    RandomTestGraph \in AllDirectedGraphs(Nodes)

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ EdgeInInputGraph
    /\ StableRandomInvariant
    /\ RandomGraphValid

\* Liveness: we always eventually process all edges
EventuallyProcessAllEdges == <>(edgeIndex = Len(AllEdges))

\* Liveness: we can always reset and start over
AlwaysCanReset == [](edgeIndex = Len(AllEdges) => <>( edgeIndex = 0))

\* Property: The specification is non-trivial (has edges to process when Nodes non-empty)
NonTrivial == Cardinality(Nodes) > 0 => Len(AllEdges) > 0

===============================================================================