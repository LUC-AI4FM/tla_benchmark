------------------------------- MODULE BoundedSequencesAndGraphs -------------------------------

CONSTANTS Graph, TestGraph

VARIABLES x, y

(*--algorithm TinyStateSystem

variables x \in {}, y \in {}

Init == /\ x \in Seq(Graph)
        /\ y \in Seq(Graph)

Next == \/ /\ x' = <<>>
            /\ y' = TLCEval(RandomElement(Seq(Graph)), <<>>)
          \/ /\ x' = Append(x, TLCEval(RandomElement(Graph), x))
            /\ y' = Append(y, TLCEval(RandomElement(Graph), y))

Inv ==
    /\ x \in Seq(Graph)
    /\ y \in Seq(Graph)
    /\ Cardinality({s \in SUBSEQ(x) : s \in Seq(TestGraph)}) = 3

Assume Cardinality({s \in SUBSEQ(Seq(Graph)) : s \in Seq(TestGraph)}) = 3

end algorithm *)

=============================================================================