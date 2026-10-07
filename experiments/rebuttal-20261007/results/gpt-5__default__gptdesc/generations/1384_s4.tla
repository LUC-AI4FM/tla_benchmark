------------------------------ MODULE TinyGraphBSeq ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  Helper operators for bounded sequences and directed graphs.
  The spec uses TLC-specific TLCEval and RandomElement to force evaluation.
*)

CONSTANTS
    NODES,            \* Node set of the constant graph
    EDGES,            \* Edge set (subset of NODES \X NODES), non-empty
    BaseSet,          \* Base set for bounded sequences (finite)
    K, L,             \* Bounds for nested bounded-sequence construction
    NestedBSeqCard    \* Fixed, TLC-evaluated cardinality of nested BSeq

(*
  BSeq(S, n) is the set of all sequences over S of length at most n.
  Note: 0..n includes 0, and [1..0 -> S] is the unique empty function.
*)
BSeq(S, n) ==
  UNION { [1..k -> S] : k \in 0..n }

(*
  Directed graph helpers: graphs are records [nodes |-> N, edges |-> E],
  where edges are ordered pairs <<u,v>> in N \X N.
*)
Graph(N, E) ==
  [nodes |-> N, edges |-> E]

Nodes(G) == G.nodes
Edges(G) == G.edges

Src(e) == e[1]
Dst(e) == e[2]

IsGraph(G) ==
  /\ IsFiniteSet(G.nodes)
  /\ G.edges \subseteq (G.nodes \X G.nodes)

(*
  A derived test graph whose definition references TLCEval(RandomElement(...))
  to force TLC evaluation in a particular constant context. The edge set is
  intentionally equal to the original edge set, but depends on a TLC-evaluated
  random node to exercise caching-sensitive evaluation paths.
*)
DerivedTestGraph(G) ==
  LET r == TLCEval(RandomElement(G.nodes))
  IN [ nodes |-> G.nodes
     , edges |-> { e \in G.edges : e \in G.edges /\ r \in G.nodes }
     ]

(*
  Constant graph and derived test graph.
*)
ConstGraph == Graph(NODES, EDGES)
TestGraph  == DerivedTestGraph(ConstGraph)

(*
  Assumptions about the constant parameters. In particular, we assume:
  - EDGES is a non-empty subset of NODES \X NODES.
  - BaseSet is finite; K and L are natural numbers (bounds).
  - NestedBSeqCard is fixed to the TLC-evaluated cardinality of the nested bounded sequence.
*)
ASSUME
  /\ IsFiniteSet(NODES)
  /\ EDGES \subseteq (NODES \X NODES)
  /\ EDGES # {}
  /\ IsFiniteSet(BaseSet)
  /\ K \in Nat
  /\ L \in Nat
  /\ NestedBSeqCard = TLCEval(Cardinality(BSeq(BSeq(BaseSet, K), L)))

VARIABLES
  e1, e2

Vars == << e1, e2 >>

Init ==
  /\ e1 \in EDGES
  /\ e2 \in EDGES

Next ==
  /\ e1' \in EDGES
  /\ e2' \in EDGES

Spec ==
  Init /\ [][Next]_Vars

(*
  Safety invariants:
  - Variables remain in the edge set type.
  - Variables are also members of the derived test graph's edge set.
  - The TLC-evaluated cardinality of the nested bounded sequence matches the fixed value.
*)
TypeInv ==
  /\ e1 \in EDGES
  /\ e2 \in EDGES

DerivedInv ==
  /\ e1 \in Edges(TestGraph)
  /\ e2 \in Edges(TestGraph)

CardinalityInv ==
  TLCEval(Cardinality(BSeq(BSeq(BaseSet, K), L))) = NestedBSeqCard

Inv == TypeInv /\ DerivedInv /\ CardinalityInv

=============================================================================