----------------------------- MODULE NondetGraphPick -----------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Nodes,       \* finite set of nodes
  FixedEdges,  \* designated fixed directed graph's edge set (subset of Nodes \X Nodes)
  AuxEdges     \* externally chosen auxiliary graph's edge set (subset of Nodes \X Nodes)

(*
  Structural assumptions about the parameterized graphs and node set.
  The auxiliary graph is allowed to differ from the fixed graph, but must
  contain it so that the cross-graph consistency invariant holds for all steps.
*)
ASSUME
  /\ IsFiniteSet(Nodes)
  /\ Nodes # {}
  /\ FixedEdges \subseteq Nodes \X Nodes
  /\ IsFiniteSet(FixedEdges)
  /\ AuxEdges \subseteq Nodes \X Nodes
  /\ FixedEdges \subseteq AuxEdges

(*
  Optional named graph records for clarity.
*)
FixedGraph == [ V |-> Nodes, E |-> FixedEdges ]
AuxGraph   == [ V |-> Nodes, E |-> AuxEdges   ]

VARIABLES
  e1, e2   \* each agent's currently held edge (always a concrete edge)

Init ==
  /\ e1 \in FixedEdges
  /\ e2 \in FixedEdges

(*
  In each step, both agents (independently and nondeterministically) select
  any edge from the fixed graph; they may also retain their current edge.
*)
Next ==
  /\ e1' \in FixedEdges
  /\ e2' \in FixedEdges

Spec == Init /\ [][Next]_<<e1, e2>>

(*
  Invariants
*)

\* Safety: each agent’s edge is always in the fixed graph.
SafetyInv ==
  /\ e1 \in FixedEdges
  /\ e2 \in FixedEdges

\* Cross-graph consistency: each agent’s edge is also in the auxiliary graph.
CrossInv ==
  /\ e1 \in AuxEdges
  /\ e2 \in AuxEdges

\* Deterministic numeric assertion over bounded sequences.
NumericExpr == Cardinality({ s \in Seq({0, 1}) : Len(s) <= 2 })
NumericInv  == NumericExpr = 7

Inv == SafetyInv /\ CrossInv /\ NumericInv

(*
  Optional theorems stating the invariants hold under Spec.
  (Proofs can be discharged with a prover; omitted here.)
*)
THEOREM Spec => []SafetyInv
THEOREM Spec => []CrossInv
THEOREM Spec => []NumericInv

=============================================================================