------------------------------ MODULE GraphSpec ------------------------------
EXTENDS Naturals, TLC, FiniteSets

CONSTANTS Graph

(* ------------------------------------------------------------------ *)
(* Helper operator that turns a set into a sequence of its elements   *)
SeqFromSet[S] == <<x \in S : x>>

(* ------------------------------------------------------------------ *)
(* Derived test graph: reverse each edge in Graph                     *)
TestGraph == {<<y,x>> \in Graph : TRUE}

(* ------------------------------------------------------------------ *)
(* Random element operator                                            *)
RandomElement[S] == CHOOSE x \in S : TRUE

(* ------------------------------------------------------------------ *)
(* Assumption about the cardinality of the graph                      *)
AssumeCardinality == TLCEval(#(Graph), [ ]) = 3

(* ------------------------------------------------------------------ *)
VARIABLE v1, v2

Init ==
    /\ v1 \in Graph
    /\ v2 \in Graph

Next ==
    \/ /\ v1' = RandomElement[Graph]
       /\ v2' = v2
    \/ /\ v2' = RandomElement[Graph]
       /\ v1' = v1

Inv ==
    /\ v1 \in Graph
    /\ v2 \in Graph
    /\ v1 \in TestGraph
    /\ v2 \in TestGraph
    /\ TLCEval(#(TestGraph), [ ]) = TLCEval(#(Graph), [ ])

(* ------------------------------------------------------------------ *)
(* Note: The use of TLCEval forces evaluation in the current context,
   ensuring that caching does not affect the cardinality check.       *)

=============================================================================