------------------------------ MODULE HelperGraphsTinyState ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
Helper operators for bounded sequences
*)
BSeq(N, S) ==
  UNION { [1..k -> S] : k \in 0..N }

(*
Directed graph helpers
A directed graph is represented as a record:
  [ V |-> set of vertices, E |-> subset of V \X V ]
*)
Vertices(g) == g.V
Edges(g) == g.E

IsDirGraph(g) ==
  /\ g \in [V: SUBSET Nat, E: SUBSET (g.V \X g.V)]
  /\ IsFiniteSet(g.V)

TestGraph(g) ==
  [ V |-> g.V,
    E |-> { e \in (g.V \X g.V) : e \in g.E } ]

(*
Anchor used to force evaluation in a particular state context.
RandomElement is applied to Edges(G) to make the evaluation depend on the current state,
but the numeric result remains the fixed cardinality due to the + IF ... THEN 0 ELSE 1 trick.
TLC's caching behavior of TLCEval and RandomElement matters for correctness of CardOK.
*)
AnchorCard(g) ==
  TLCEval(
    Cardinality(BSeq(2, BSeq(3, {1, 2})))
    + IF RandomElement(Edges(g)) \in Edges(g) THEN 0 ELSE 1
  )

ExpectedCard == 241

(*
Assumption about the cardinality of a nested bounded-sequence construction.
|BSeq(3, {1,2})| = 1 + 2 + 4 + 8 = 15
|BSeq(2, BSeq(3, {1,2}))| = 1 + 15 + 225 = 241
*)
ASSUME Cardinality(BSeq(2, BSeq(3, {1, 2}))) = 241

CONSTANT G

ASSUME
  /\ IsDirGraph(G)
  /\ Edges(G) # {}  \* ensure RandomElement is applied to a non-empty finite set

VARIABLES e1, e2

vars == << e1, e2 >>

Init ==
  /\ e1 \in Edges(G)
  /\ e2 \in Edges(G)

Next ==
  /\ e1' \in Edges(G)
  /\ e2' \in Edges(G)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ e1 \in Edges(G)
  /\ e2 \in Edges(G)

InTest ==
  /\ e1 \in TestGraph(G).E
  /\ e2 \in TestGraph(G).E

(*
This invariant combines:
- type membership,
- membership in a derived test graph, and
- a fixed TLCEval-computed cardinality check that is evaluated in a state-dependent context.
Additionally, the final conjunct forces TLC to touch RandomElement within TLCEval each state,
but it always evaluates to TRUE.
*)
CardOK ==
  /\ AnchorCard(G) = ExpectedCard
  /\ TLCEval(IF RandomElement(Edges(G)) \in Edges(G) THEN TRUE ELSE FALSE)

Inv == TypeOK /\ InTest /\ CardOK

======================================