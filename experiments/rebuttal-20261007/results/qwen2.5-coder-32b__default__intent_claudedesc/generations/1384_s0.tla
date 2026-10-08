------------------------------- MODULE TLCEvalCaching ------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Nodes,          \* The set of nodes in the graph
    MaxLength       \* The maximum length for bounded sequences

VARIABLES 
    TestGraph,      \* The randomly selected test graph
    Edges           \* The current set of edges being considered

Init == 
    /\ TestGraph \in SUBSET [Nodes -> Nodes]
    /\ Edges = {}

Next ==
    \/ \E seq \in Seq(Nodes) : Len(seq) <= MaxLength /\ Edges' = {seq}
    \/ \E graph \in SUBSET [Nodes -> Nodes] : TestGraph' = graph

Spec == 
    Init /\ [][Next]_<<TestGraph>>

\* Mathematical correctness properties
Prop1 ==
    LET DoubleNestedSeqs == { seq \in Seq(Seq(Nodes)) | Len(seq) <= 2 /\ \A s \in seq : Len(s) <= 2 }
    IN Cardinality(DoubleNestedSeqs) = 57

Prop2 ==
    LET TripleNestedSeqs == { seq \in Seq(Seq(Seq(Nodes))) | Len(seq) <= 3 /\ \A s1 \in seq : \A s2 \in s1 : Len(s2) <= 3 }
    IN Cardinality(TripleNestedSeqs) = 65641

\* Invariant stability property
Stability ==
    Edges \subseteq TestGraph

\* Deterministic behavior of the test graph
Determinism ==
    \/ UNCHANGED TestGraph
    \/ /\ TestGraph' = CHOOSE g \in SUBSET [Nodes -> Nodes] : TRUE
       /\ UNCHANGED Edges

Invariant == 
    Stability /\ Determinism

Liveness ==
    <>(Cardinality(Edges) = 57)

Fairness ==
    WF_next(Next)

THEOREM Spec => []Invariant
THEOREM Spec => Liveness
THEOREM Spec => Fairness

=============================================================================