---------------------------- MODULE BoundedSeqGraphSpec ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

\* Helper operators for bounded sequences
BoundedSeq(S, n) == UNION {[1..m -> S] : m \in 0..n}

\* Helper operators for directed graphs
DirectedGraph(Nodes) == [nodes : SUBSET Nodes, edges : SUBSET (Nodes \X Nodes)]

Edges(G) == G.edges

\* Constants for the graph
CONSTANTS Nodes

\* Define a constant graph based on Nodes
ConstGraph == [nodes |-> Nodes, edges |-> Nodes \X Nodes]

\* Variables ranging over the edge set
VARIABLES x, y

vars == <<x, y>>

\* The edge set of the constant graph
EdgeSet == Edges(ConstGraph)

\* Assumption about cardinality of nested bounded-sequence construction
\* This checks that the nested construction has expected cardinality
ASSUME Cardinality(BoundedSeq(BoundedSeq({1, 2}, 2), 2)) > 0

\* Test graph derived from current state
\* The caching behavior of TLCEval matters for correctness of the invariant
TestGraph == [nodes |-> Nodes, edges |-> {e \in EdgeSet : e[1] \in Nodes /\ e[2] \in Nodes}]

TestEdges == TLCEval(Edges(TestGraph))

\* Fixed cardinality computation using TLCEval
\* Caching ensures this is evaluated once and reused
FixedCard == TLCEval(Cardinality(EdgeSet))

\* Type invariant checking membership in edge set
TypeOK == /\ x \in EdgeSet
          /\ y \in EdgeSet

\* Main invariant combining type membership and derived graph membership
\* The TLCEval-computed cardinality check is included
Invariant == /\ TypeOK
             /\ x \in TestEdges
             /\ y \in TestEdges
             /\ FixedCard = Cardinality(Nodes) * Cardinality(Nodes)

\* Initial state: select edges from the edge set
\* Uses RandomElement to force evaluation in TLC context
Init == /\ x = IF EdgeSet # {} 
             THEN RandomElement(EdgeSet) 
             ELSE CHOOSE e \in Nodes \X Nodes : TRUE
        /\ y = IF EdgeSet # {} 
             THEN RandomElement(EdgeSet) 
             ELSE CHOOSE e \in Nodes \X Nodes : TRUE

\* Next state: transition to new edges in the edge set
\* TLCEval forces evaluation of the edge set before selection
Next == \/ /\ x' = RandomElement(TLCEval(EdgeSet))
           /\ y' = y
        \/ /\ y' = RandomElement(TLCEval(EdgeSet))
           /\ x' = x
        \/ /\ x' = RandomElement(EdgeSet)
           /\ y' = RandomElement(EdgeSet)

\* Fairness condition: weak fairness on transitions
Fairness == WF_vars(Next)

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Liveness property: the system can always make progress
Liveness == []<>(ENABLED Next)

===================================================================================