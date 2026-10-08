------------------------------ MODULE GraphEdgeHolders ------------------------------

EXTENDS Naturals, FiniteSets, TLC

(*
  Constants:
    - Nodes: a finite, nonempty set of nodes
    - Graph: the fixed directed graph for this run, a subset of Nodes × Nodes
    - TestGraph: an auxiliary directed graph (may differ), used in invariants
*)
CONSTANTS Nodes, Graph, TestGraph

(*
  Basic typing/structural constraints on constants.
  We assume TestGraph is a (possibly different) supergraph of Graph so that
  the cross-graph consistency invariant can be required and verified.
*)
IsGraph(G) == G \subseteq (Nodes \X Nodes)

ConstOK ==
  /\ IsFiniteSet(Nodes)
  /\ Nodes # {}
  /\ IsGraph(Graph)
  /\ IsGraph(TestGraph)
  /\ Graph \subseteq TestGraph
  /\ Graph # {}  \* ensure at least one initial state exists

ASSUME ConstOK

VARIABLES e1, e2

vars == << e1, e2 >>

(*
  Initial condition: each agent starts holding some edge of Graph.
*)
Init ==
  /\ e1 \in Graph
  /\ e2 \in Graph

(*
  Next-state relation: in each step, each agent independently and
  nondeterministically re-selects any edge of Graph. No ordering or
  communication constraints are imposed.
*)
Next ==
  /\ e1' \in Graph
  /\ e2' \in Graph

(*
  Invariants to be model-checked:
    - Safety: each agent’s chosen edge is in the fixed Graph.
    - Cross-graph consistency: each chosen edge is also in TestGraph.
    - Deterministic numeric assertion: a fixed integer computed from
      bounded sequences over a small finite set equals a specified constant.
      Here we use the cardinality of all length-2 sequences over {0,1},
      i.e., |{0,1} × {0,1}| = 4.
*)
Safety ==
  /\ e1 \in Graph
  /\ e2 \in Graph

CrossConsistency ==
  /\ e1 \in TestGraph
  /\ e2 \in TestGraph

StableCount ==
  LET S == {0, 1} IN Cardinality(S \X S)

Numeric ==
  StableCount = 4

Inv == Safety /\ CrossConsistency /\ Numeric

Spec == Init /\ [][Next]_vars

THEOREM InvIsInvariant == Spec => []Inv

=============================================================================