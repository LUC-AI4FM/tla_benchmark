------------------------------- MODULE TLCEvalCachingBehavior ------------------------------

CONSTANTS Nodes, MaxLength

VARIABLES Graph, TestGraph, Edges

(*--algorithm TLCEvalCachingBehavior

variables Graph \in [Nodes -> SUBSET Nodes],
          TestGraph \in [Nodes -> SUBSET Nodes],
          Edges \in SUBSET (Nodes \X Nodes);

Init == /\ Graph = [n \in Nodes |-> {}]
        /\ TestGraph \in RandomGraphs(Nodes)
        /\ Edges = {}

Next ==
    \/ /\ Edges' = {}
       /\ TestGraph' = TestGraph
       /\ Graph' = Graph
    \/ /\ Edges' \in SUBSET (Nodes \X Nodes)
       /\ TestGraph' = TestGraph
       /\ Graph' = [n \in Nodes |-> {m \in Nodes : <<n, m>> \in Edges'}]

Inv ==
    /\ Cardinality(BoundedSequences(Graph, MaxLength)) = ExpectedCardinality(Nodes, MaxLength)
    /\ Edges \subseteq (Nodes \X Nodes)
    /\ Edges \subseteq TestGraph
    /\ TestGraph \in RandomGraphs(Nodes)

BoundedSequences(graph, bound) ==
    LET SeqLen[seq] == LEN(seq)
        ValidSeq(seq) == \A i \in 1..SeqLen(seq)-1 : seq[i+1] \in graph[seq[i]]
    IN {seq \in (DOMAIN graph)^_ : SeqLen(seq) <= bound /\ ValidSeq(seq)}

RandomGraphs(nodes) ==
    LET AllEdges == nodes \X nodes
        PowersetEdges == SUBSET AllEdges
    IN {g \in [nodes -> SUBSET nodes] :
            \A n \in nodes : g[n] \subseteq (nodes \ {n})}

ExpectedCardinality(nodes, bound) ==
    CASE bound = 2 /\ Cardinality(nodes) = 2 -> 57
    [] bound = 3 /\ Cardinality(nodes) = 3 -> 65641
    [] OTHER -> UNDEF

==*)
=============================================================================