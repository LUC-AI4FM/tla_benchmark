---- MODULE GraphBSeqTiny ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  Helper operators for bounded sequences and directed graphs.
  The spec also demonstrates TLC-specific evaluation with TLCEval and RandomElement.
  Caching behavior of TLCEval can matter for correctness of invariants that depend
  on evaluation context; see TestGraph and FixedCardCheck below.
*)

CONSTANTS U, G

(*
  Directed graph helpers
*)
IsDirectedGraph(g) ==
  /\ g \in [Nodes: SUBSET U, Edges: SUBSET (U \X U)]
  /\ g.Edges \subseteq g.Nodes \X g.Nodes

Nodes(g) == g.Nodes

Edges(g) == g.Edges

Edge(u, v) == <<u, v>>

OutNeighbors(g, u) == { v \in g.Nodes : <<u, v>> \in g.Edges }

(*
  TestGraph forces TLC to evaluate the edge set in a particular call-site context
  by combining RandomElement (to bind an evaluation context) and TLCEval.
  This constructs a graph with the same nodes and edges as g but forces a TLC evaluation
  path that is relevant when caching is involved.
*)
TestGraph(g) ==
  [ Nodes |-> g.Nodes,
    Edges |-> LET _ctx == TLCEval(RandomElement(g.Edges))
              IN TLCEval(g.Edges) ]

(*
  Bounded sequences: sequences over S of length at most n.
*)
BSeq(S, n) ==
  IF n \in Nat THEN UNION { [1..k -> S] : k \in 0..n } ELSE {}

(*
  A nested bounded-sequence construction used for a fixed cardinality check.
  For S = {1,2} and bound 2, |BSeq(S,2)| = 1 + 2 + 4 = 7.
  Nesting once more with bound 2 yields 1 + 7 + 49 = 57.
*)
NestedBSeq == BSeq(BSeq({1, 2}, 2), 2)

(*
  Assumptions about the constant graph and the nested bounded sequence.
*)
ASSUME
  /\ IsDirectedGraph(G)
  /\ Cardinality(G.Edges) > 0
  /\ Cardinality(NestedBSeq) = 57

(*
  State variables: a tiny state system with two variables ranging over the edge set.
*)
VARIABLES x, y

(*
  Initial states: pick any edges for x and y.
*)
Init ==
  /\ x \in G.Edges
  /\ y \in G.Edges

(*
  Next-state relation: in each step, update either x or y to any edge, leaving the other unchanged.
*)
Next ==
  \/ /\ x' \in G.Edges
     /\ y' = y
  \/ /\ y' \in G.Edges
     /\ x' = x

Spec == Init /\ [][Next]_<<x, y>>

(*
  Safety invariants:
    - TypeInv: x and y always range over the edge set of the constant graph G.
    - DerivedMembershipInv: x and y are also members of the edge set of the derived TestGraph(G).
    - FixedCardCheck: a fixed TLCEval-computed cardinality check for NestedBSeq.
      TLCEval here forces TLC to compute the cardinality in a fixed context; the equality
      to 57 is intended to be constant across states and sensitive to caching if misused.
*)
TypeInv == /\ x \in G.Edges /\ y \in G.Edges

DerivedMembershipInv ==
  /\ x \in TestGraph(G).Edges
  /\ y \in TestGraph(G).Edges

FixedCardCheck ==
  TLCEval(Cardinality(NestedBSeq)) = 57

Inv == TypeInv /\ DerivedMembershipInv /\ FixedCardCheck

====