---------------------------- MODULE GraphHelpers ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Helper operators for bounded sequences                                  *)
(***************************************************************************)

\* The set of all sequences of elements from S with length at most n
BoundedSeq(S, n) == UNION {[1..i -> S] : i \in 0..n}

\* The set of all sequences of elements from S with exactly length n
SeqOfLen(S, n) == [1..n -> S]

(***************************************************************************)
(* Helper operators for directed graphs                                    *)
(***************************************************************************)

\* A directed graph is represented as a record with nodes and edges
\* where edges is a set of pairs <<from, to>>
DirectedGraph(Nodes, Edges) == [nodes |-> Nodes, edges |-> Edges]

\* The set of all possible edges for a set of nodes
AllEdges(Nodes) == Nodes \X Nodes

\* The edge set of a graph
EdgeSet(G) == G.edges

\* The node set of a graph
NodeSet(G) == G.nodes

\* Successor nodes - nodes reachable in one step from n
Successors(G, n) == {m \in G.nodes : <<n, m>> \in G.edges}

\* Predecessor nodes - nodes that can reach n in one step
Predecessors(G, n) == {m \in G.nodes : <<m, n>> \in G.edges}

(***************************************************************************)
(* Constants for the graph specification                                   *)
(***************************************************************************)

CONSTANTS 
    GraphNodes,     \* The set of nodes in the constant graph
    GraphEdges      \* The set of edges in the constant graph (subset of GraphNodes x GraphNodes)

\* The constant graph G
G == DirectedGraph(GraphNodes, GraphEdges)

(***************************************************************************)
(* Assumption about cardinality of nested bounded-sequence construction    *)
(* This tests that the cardinality computation works correctly for         *)
(* nested bounded sequences, which exercises caching behavior              *)
(***************************************************************************)

ASSUME Cardinality(BoundedSeq(BoundedSeq({1,2}, 2), 2)) > 0

(***************************************************************************)
(* Variables for the state system                                          *)
(***************************************************************************)

VARIABLES x, y

vars == <<x, y>>

(***************************************************************************)
(* Type definitions                                                        *)
(***************************************************************************)

\* Both x and y range over the edge set of the constant graph G
TypeOK == /\ x \in EdgeSet(G)
          /\ y \in EdgeSet(G)

(***************************************************************************)
(* Test graph derived from the current state                               *)
(* The caching behavior of TLCEval matters for correctness here            *)
(***************************************************************************)

\* A test graph derived from current edges - includes edges where
\* the source of x connects to targets reachable via y
TestGraphEdges == 
    LET 
        \* Force evaluation via TLCEval - caching matters for correctness
        baseEdges == TLCEval(EdgeSet(G))
    IN
        {e \in baseEdges : e[1] = x[1] \/ e[2] = y[2]}

TestGraph == DirectedGraph(GraphNodes, TestGraphEdges)

(***************************************************************************)
(* Initial state predicate                                                 *)
(***************************************************************************)

Init == 
    /\ x \in EdgeSet(G)
    /\ y \in EdgeSet(G)

(***************************************************************************)
(* Next state relation                                                     *)
(* Uses RandomElement to non-deterministically select edges                *)
(* TLCEval forces evaluation in particular context                         *)
(***************************************************************************)

Next ==
    \/ /\ x' = TLCEval(RandomElement(EdgeSet(G)))
       /\ y' = y
    \/ /\ y' = TLCEval(RandomElement(EdgeSet(G)))
       /\ x' = x
    \/ /\ x' = TLCEval(RandomElement(EdgeSet(G)))
       /\ y' = TLCEval(RandomElement(EdgeSet(G)))

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

\* Fixed TLCEval-computed cardinality check
\* The cardinality of the edge set should remain consistent
CardinalityCheck == TLCEval(Cardinality(EdgeSet(G))) = Cardinality(GraphEdges)

\* Main invariant: type membership and membership in derived test graph
\* The caching behavior of TLCEval is important for this invariant
Inv == 
    /\ TypeOK
    /\ x \in EdgeSet(TestGraph)
    /\ y \in EdgeSet(TestGraph)
    /\ CardinalityCheck

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

Safety == Inv

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* Eventually, x and y may change (with fairness, the system keeps evolving)
Liveness == <>(\E e \in EdgeSet(G) : x = e)

=============================================================================