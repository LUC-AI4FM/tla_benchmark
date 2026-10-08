------------------------------ MODULE TinyStateSystem ------------------------------

EXTENDS Sequences, FiniteSets, TLC

CONSTANTS GRAPH, CARDINALITY_ASSUMPTION

VARIABLES v1, v2

(*--algorithm TinyStateSystem
variables v1 \in Edges(GRAPH), v2 \in Edges(GRAPH)
begin
    Init:
        with \* Initialize variables to random edges from the graph
            u \in Edges(GRAPH),
            w \in Edges(GRAPH)
        do
            v1 := u;
            v2 := w
        end with;

    Next ==
        /\ \/ /\ TLC!TLCEval(v1 = RandomElement(Edges(GRAPH)))
               /\ TLC!TLCEval(v2 = RandomElement(Edges(GRAPH)))
           \/ /\ TLC!TLCEval(v1 \in Preds(GRAPH, v2))
              /\ TLC!TLCEval(v2 \in Succs(GRAPH, v1))
        /\ TYPEOK
        /\ IN_GRAPH

    TYPEOK ==
        /\ v1 \in Edges(GRAPH)
        /\ v2 \in Edges(GRAPH)

    IN_GRAPH ==
        /\ \/ /\ TLC!TLCEval(Cardinality({e \in SUBSET Edges(GRAPH) : TLC!TLCEval(e = <<v1, v2>>)}) = CARDINALITY_ASSUMPTION)
           \/ /\ TLC!TLCEval(Cardinality({e \in SUBSET Edges(GRAPH) : TLC!TLCEval(e = <<v2, v1>>)}) = CARDINALITY_ASSUMPTION)

end algorithm;*)

Init == 
    \E u \in Edges(GRAPH), w \in Edges(GRAPH):
        /\ v1 = u
        /\ v2 = w

Next ==
    \/ TLC!TLCEval(v1 = RandomElement(Edges(GRAPH)))
       /\ TLC!TLCEval(v2 = RandomElement(Edges(GRAPH)))
    \/ TLC!TLCEval(v1 \in Preds(GRAPH, v2))
       /\ TLC!TLCEval(v2 \in Succs(GRAPH, v1))

TYPEOK ==
    /\ v1 \in Edges(GRAPH)
    /\ v2 \in Edges(GRAPH)

IN_GRAPH ==
    TLC!TLCEval(Cardinality({e \in SUBSET Edges(GRAPH) : TLC!TLCEval(e = <<v1, v2>>)}) = CARDINALITY_ASSUMPTION)

Spec ==
    Init /\ [][Next]_<<v1, v2>> /\ Stable(IN_GRAPH) /\ WF_(Next, <<v1, v2>>)
    
================================================================================