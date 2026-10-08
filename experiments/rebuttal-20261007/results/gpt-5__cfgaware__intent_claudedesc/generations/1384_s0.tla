---- MODULE TLCEvalCache ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*
  This module verifies:
  - Correct cardinalities for nested bounded sequences via TLCEval.
  - Stability of a randomly selected graph (via TLC!RandomElement) across
    multiple evaluations and across steps, relying on TLCEval caching.
*)

VARIABLES e, tg

(*
  Bounded sequences of length 0..n over S.
*)
BoundedSeqs(S, n) == { s \in Seq(S) : Len(s) <= n }

(*
  Context-sensitive caching checks for bounded sequences:
    - Over {1,2} with bound 2, then bounded again with bound 2 -> 57
    - Over {1,2,3} with bound 3, then bounded again with bound 3 -> 65641
  We explicitly wrap the constructions in TLCEval to exercise TLC's caching
  for context-dependent expressions.
*)
DoubleBoundedOverTwo == TLCEval(BoundedSeqs({1,2}, 2))
DoubleNestedTwo == TLCEval(BoundedSeqs(DoubleBoundedOverTwo, 2))
Check57 == Cardinality(DoubleNestedTwo) = 57

TripleBoundedOverThree == TLCEval(BoundedSeqs({1,2,3}, 3))
TripleNestedThree == TLCEval(BoundedSeqs(TripleBoundedOverThree, 3))
Check65641 == Cardinality(TripleNestedThree) = 65641

(*
  Directed graphs over a fixed set of nodes; graphs are sets of directed edges.
*)
Nodes == {1, 2, 3}
Edges == Nodes \X Nodes

(*
  Input graph: use the complete directed graph to ensure non-empty edge set.
*)
Graph == Edges

AllGraphs == SUBSET Edges
NonEmptyGraphs == { g \in AllGraphs : g # {} }

(*
  Randomly selected test graph, required to remain stable across the run.
  TLCEval(RandomElement(...)) ensures TLC picks a concrete graph once and,
  with correct caching, reuses that same value for all subsequent evaluations.
*)
TestGraph == TLCEval(RandomElement(NonEmptyGraphs))

(*
  Initialization:
    - Pick an initial edge from both Graph and TestGraph.
    - Snapshot the chosen TestGraph into a state variable 'tg' to assert
      cross-step stability (tg is kept unchanged).
    - Assert the bounded-sequence cardinality checks up front as well.
*)
Init ==
  /\ e \in Graph \cap TestGraph
  /\ tg = TestGraph
  /\ Check57
  /\ Check65641

(*
  Next-step relation:
    - Always pick the next edge from the intersection of Graph and TestGraph.
    - Keep tg unchanged to detect any unintended changes in TestGraph across steps.
*)
Next ==
  /\ e' \in Graph \cap TestGraph
  /\ tg' = tg

(*
  Invariant:
    - Edge is always an edge of both Graph and TestGraph (guards against instability
      if TestGraph were re-evaluated differently within the same state).
    - tg equals TestGraph in every state (guards against cross-step instability).
    - Cardinality checks for nested bounded sequences hold.
*)
Inv ==
  /\ e \in Graph
  /\ e \in TestGraph
  /\ tg = TestGraph
  /\ Check57
  /\ Check65641
  /\ TestGraph \in NonEmptyGraphs

====