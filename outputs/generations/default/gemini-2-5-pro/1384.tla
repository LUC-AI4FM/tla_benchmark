---- MODULE BoundedGraphSystem ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* This module defines helper operators for sequences and graphs, and then *)
(* specifies a system with two variables that range over the edges of a    *)
(* constant graph. It uses TLC-specific operators like TLCEval to          *)
(* demonstrate forcing evaluation in a particular context, where caching   *)
(* behavior can be relevant to a model's performance or correctness.       *)
(***************************************************************************)

----
(* Helper Operators for Graphs and Sequences *)

\* The set of all sequences of length `n` with elements from set `S`.
BoundedSeq(S, n) == [1..n -> S]

\* The set of all directed graphs (represented as adjacency maps) on vertex set `V`.
DirectedGraph(V) == [V -> SUBSET V]

\* The set of edges for a graph `G` represented as an adjacency map.
Edges(G) == {<<v, w>> : v \in DOMAIN G, w \in G[v]}

\* A predicate to check if G is a valid directed graph on its own vertex set.
IsDirectedGraph(G) == \A v \in DOMAIN G : G[v] \subseteq DOMAIN G

\* The set of vertices of a graph `G`.
Vertices(G) == DOMAIN G

----
(* TLC-Specific Operators *)

\* TLCEval(expr) is a special operator interpreted by TLC. For the TLA+
\* parser (SANY), we define it as the identity function. In TLC, it forces
\* the evaluation of its argument `expr` at the point it appears. This can
\* be used to control TLC's evaluation strategy, which may be important
\* when the caching of expression results affects the model's behavior.
TLCEval(expr) == expr

\* RandomElement(S) is a special operator interpreted by TLC to pick a
\* non-deterministic but fixed element from a set S for the duration of a
\* single state's evaluation. For SANY, we model it as an arbitrary choice.
RandomElement(S) == CHOOSE x \in S : TRUE

----
(* System Constants and Assumptions *)

CONSTANTS
  V,      \* The set of vertices.
  Graph   \* A constant directed graph on V.

ASSUME
  /\ IsDirectedGraph(Graph)
  /\ V = Vertices(Graph)

\* An assumption about the cardinality of a nested bounded-sequence construction.
ASSUME Cardinality(BoundedSeq(BoundedSeq(V, 2), 2)) = (Cardinality(V)^2)^2

----
(* System Variables *)

VARIABLES
  x,      \* A variable representing an edge in the graph.
  y       \* A second variable representing an edge in the graph.

vars == <<x, y>>

----
(* Derived Definitions *)

\* A derived graph consisting of all edges from the base `Graph` except for self-loops.
TestGraphEdges == { e \in Edges(Graph) : e[1] # e[2] }

----
(* System Specification *)

\* The initial state predicate.
Init ==
  /\ x \in TestGraphEdges
  /\ y \in TestGraphEdges

\* The next-state relation. In each step, x and y can be non-deterministically
\* reassigned to any edge in the TestGraphEdges set.
Next ==
  /\ x' \in TestGraphEdges
  /\ y' \in TestGraphEdges

\* The complete system specification, allowing stuttering steps.
Spec == Init /\ [][Next]_vars

----
(* Properties *)

\* This invariant asserts several properties of the system state:
\* 1. Type Membership: `x` and `y` are always valid edges of the base `Graph`.
\* 2. Test Graph Membership: `x` and `y` belong to the more restrictive set
\*    `TestGraphEdges` (edges that are not self-loops).
\* 3. Cardinality Check: A fixed, constant property about the graph is checked.
\*    It is wrapped in TLCEval to illustrate forcing evaluation. In a more
\*    complex model, this could be used to ensure a property is checked
*    against a fully-evaluated state before other expressions are, as TLC's
*    caching of the value of `E` could be observable.
Invariant ==
  /\ x \in Edges(Graph)
  /\ y \in Edges(Graph)
  /\ x \in TestGraphEdges
  /\ y \in TestGraphEdges
  /\ LET E == Edges(Graph)
     IN TLCEval(Cardinality({s \in BoundedSeq(E, 2) : s[1] = s[2]})) = Cardinality(E)

=============================================================================