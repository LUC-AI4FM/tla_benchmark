---------------------------- MODULE GraphHelper ----------------------------

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS GRAPH, EDGES

VARIABLES edge1, edge2

Init == /\ edge1 \in EDGES
        /\ edge2 \in EDGES

Next == \/ CHOOSE newEdge \in EDGES : edge1' = newEdge /\ edge2' = edge2
        \/ CHOOSE newEdge \in EDGES : edge1' = edge1  /\ edge2' = newEdge

Spec == Init /\ [][Next]_<<edge1, edge2>>

(*--algorithm GraphHelper
variables edge1, edge2;
begin
    with edge1 \in EDGES, edge2 \in EDGES do
        while TRUE do
            either edge1 := CHOOSE newEdge \in EDGES : newEdge;
                   or edge2 := CHOOSE newEdge \in EDGES : newEdge;
end algorithm*)

Invariant ==
    /\ edge1 \in EDGES
    /\ edge2 \in EDGES
    /\ LET derivedGraph == { <<edge1, edge2>> } \cup { <<edge2, edge1>> }
       IN derivedGraph \subseteq GRAPH

CardinalityAssumption ==
    ASSUME Cardinality({s \in [1..2 -> {1..3}] : s[1] < s[2]}) = 3

TypeOK == /\ edge1 \in EDGES
           /\ edge2 \in EDGES

TestGraphMembership ==
    LET derivedGraph == { <<edge1, edge2>> } \cup { <<edge2, edge1>> }
    IN derivedGraph \subseteq GRAPH

CardinalityCheck ==
    LET testSet == {s \in [1..2 -> {1..3}] : s[1] < s[2]}
    IN TLCEval(Cardinality(testSet)) = 3

Fairness == WF_next(<<edge1, edge2>>)

=============================================================================