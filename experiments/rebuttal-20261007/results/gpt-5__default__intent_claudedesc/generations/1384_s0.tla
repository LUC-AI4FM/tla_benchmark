------------------------------ MODULE TLCEvalCacheVerification ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Nodes,      \* Set of nodes
  InGraph     \* Input directed graph: a set of edges (pairs) over Nodes

VARIABLES
  e,          \* A state variable ranging over edges
  RG          \* A state variable holding the selected random test graph (must remain constant)

(*
  BSeq(S, n) = set of all sequences over S with length in 0..n
*)
BSeq(S, n) ==
  UNION { [1..k -> S] : k \in 0..n }

GraphEdges(N) == SUBSET (N \X N)

RandomGraph(N) == RandomElement(GraphEdges(N))

(*
  TLCEval ensures the chosen graph is evaluated once and then cached
  so that repeated references return the same graph throughout the run.
*)
TestGraph == TLCEval(RandomGraph(Nodes))

EdgesBoth == InGraph \cap TestGraph

(*
  Mathematical correctness of bounded sequences under nested construction.
  These use TLCEval to ensure context-sensitive caching is honored for different
  parameters and depths.
*)
SeqCardinalityOK_2Over2 ==
  Cardinality(TLCEval(BSeq(TLCEval(BSeq({1, 2}, 2)), 2))) = 57

SeqCardinalityOK_3Over3 ==
  Cardinality(TLCEval(BSeq(TLCEval(BSeq({1, 2, 3}, 3)), 3))) = 65641

(*
  Typing and basic well-formedness conditions
*)
TypeOK ==
  /\ InGraph \subseteq (Nodes \X Nodes)
  /\ e \in (Nodes \X Nodes)
  /\ RG \subseteq (Nodes \X Nodes)

(*
  Initialization:
    - Ensure graphs are over Nodes
    - Select and store the random test graph in RG
    - Pick an initial edge from the intersection of InGraph and TestGraph
*)
Init ==
  /\ InGraph \subseteq (Nodes \X Nodes)
  /\ RG = TestGraph
  /\ EdgesBoth # {}
  /\ e \in EdgesBoth

(*
  Next step:
    - Keep the selected random graph RG unchanged
    - Choose any edge from the intersection (including possibly staying on the same edge)
*)
Next ==
  /\ UNCHANGED RG
  /\ e' \in EdgesBoth

Spec == Init /\ [][Next]_<<e, RG>>

(*
  Safety invariants:
    - Nested bounded sequences have the expected cardinalities (57 and 65641)
    - The tracked edge is always in both graphs' edge sets
    - The stored random graph equals the (cached) TestGraph at all times
*)
Inv_SeqCardinality ==
  /\ SeqCardinalityOK_2Over2
  /\ SeqCardinalityOK_3Over3

Inv_StableEdges ==
  e \in EdgesBoth

Inv_DeterministicRandomGraph ==
  RG = TestGraph

Safety ==
  /\ Inv_SeqCardinality
  /\ Inv_StableEdges
  /\ Inv_DeterministicRandomGraph

=============================================================================