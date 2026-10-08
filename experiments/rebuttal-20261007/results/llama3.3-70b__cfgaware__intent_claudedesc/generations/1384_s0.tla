---------------------------- MODULE TLCEvalCaching ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Graph, TestGraph, MaxLength, NodeSet
VARIABLE seq, testSeq, edges, testEdges

Init ==
  /\ seq = <<>>
  /\ testSeq = <<>>
  /\ edges = {}
  /\ testEdges = {}

Next ==
  /\ IF (Len(seq) < MaxLength)
    THEN seq' = Append(seq, ChooseNode(NodeSet))
    ELSE seq' = seq
  /\ testSeq' = IF (Len(testSeq) < MaxLength)
                THEN Append(testSeq, ChooseNode(NodeSet))
                ELSE testSeq
  /\ edges' = IF (edges = {})
              THEN {<<n1, n2>> : n1 \in NodeSet, n2 \in NodeSet}
              ELSE edges
  /\ testEdges' = IF (testEdges = {})
                  THEN ChooseGraph(edges)
                  ELSE testEdges

Inv ==
  /\ seq \in BoundedSequences(NodeSet, MaxLength)
  /\ testSeq \in BoundedSequences(NodeSet, MaxLength)
  /\ edges \subseteq {<<n1, n2>> : n1 \in NodeSet, n2 \in NodeSet}
  /\ testEdges \subseteq edges
  /\ StableRandomSelection(testEdges)

ChooseNode(set) == CHOOSE x \in set : TRUE

ChooseGraph(edges) == CHOOSE g \in SUBSET edges : TRUE

BoundedSequences(set, len) ==
  {<<>>} \cup UNION {i \in 1..len : {Append(s, x) : s \in BoundedSequences(set, i-1), x \in set}}

StableRandomSelection(edges) == edges = TestGraph

THEOREM CardinalityDoubleNested == 
  (Cardinality(UNION {BoundedSequences(BoundedSequences({1,2}, 2), 2)})) = 57

THEOREM CardinalityTripleNested == 
  (Cardinality(UNION {BoundedSequences(BoundedSequences(BoundedSequences({1,2,3}, 3), 3), 3)})) = 65641
================================================================================