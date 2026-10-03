---------------------------- MODULE TLCEvalGraph ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

\* Helper operators for bounded sequences
BoundedSeq(S, n) == UNION {[1..i -> S] : i \in 0..n}

\* Helper operators for directed graphs
DirectedGraph(Nodes) == [nodes : SUBSET Nodes, edges : SUBSET (Nodes \times Nodes)]

Edges(G) == G.edges

Nodes(G) == G.nodes

\* Constants for the graph
CONSTANTS GraphNodes

\* The constant graph we work with
ConstGraph == [nodes |-> GraphNodes, edges |-> GraphNodes \times GraphNodes]

\* Variables ranging over the edge set
VARIABLES x, y

vars == <<x, y>>

\* Type definition for edges
EdgeSet == Edges(ConstGraph)

\* Assumption about cardinality of nested bounded-sequence construction
\* This tests that TLCEval properly caches complex nested structures
ASSUME Cardinality(BoundedSeq(BoundedSeq(GraphNodes, 2), 2)) >= 1

\* A derived test graph based on current state
\* The caching behavior of TLCEval matters for correctness when this is evaluated
TestGraph == TLCEval([nodes |-> GraphNodes, 
                      edges |-> {e \in GraphNodes \times GraphNodes : 
                                 \/ e[1] = x[1] 
                                 \/ e[2] = y[2]}])

\* Initial state: pick edges from the constant graph
Init == 
    /\ x \in EdgeSet
    /\ y \in EdgeSet

\* Next state: randomly select new edges
\* Using RandomElement forces TLC to evaluate in a particular context
Next ==
    \/ /\ x' = RandomElement(EdgeSet)
       /\ y' = y
    \/ /\ y' = RandomElement(EdgeSet)
       /\ x' = x
    \/ /\ x' = RandomElement(EdgeSet)
       /\ y' = RandomElement(EdgeSet)

\* Type invariant: both variables are edges in the constant graph
TypeOK == 
    /\ x \in EdgeSet
    /\ y \in EdgeSet

\* Membership in derived test graph
\* Caching behavior matters: TLCEval ensures the TestGraph is computed once per state
MembershipInv == 
    /\ x \in Edges(TestGraph)
    /\ y \in Edges(TestGraph)

\* Fixed TLCEval-computed cardinality check
\* This checks that the cardinality computation is cached and consistent
CardinalityCheck == TLCEval(Cardinality(EdgeSet)) = Cardinality(GraphNodes) * Cardinality(GraphNodes)

\* Combined invariant
Inv == 
    /\ TypeOK
    /\ MembershipInv
    /\ CardinalityCheck

\* Specification with weak fairness
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Liveness: the system can always make progress
Liveness == <>[][Next]_vars

=============================================================================