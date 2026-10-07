MODULE Github648
EXTENDS Sequences, FiniteSets

CONSTANT Graph

VARIABLES v, w

(* Utility operators *)

BoundedSeq(S, n) == { s \in Seq(S) : Len(s) <= n }

BoundedSeqTLCEval(S, n) == TLCEval({ s \in Seq(S) : Len(s) <= n })

DirectedGraphs(nodes) ==
  { g \subseteq { <<x, y>> : x \in nodes /\ y \in nodes } }

RandomElement(S) == TLCEval(CHOOSE e \in S : TRUE)

TestGraph ==
  TLCEval((CHOOSE g \in DirectedGraphs({1,2,3}) : g) \/ {<<1,1>>})

(* Assumptions *)

ASSUME Cardinality(BoundedSeqTLCEval(BoundedSeqTLCEval({1,2}, 2), 2)) = 57

(* Initial state *)

Init == /\ v \in Graph
        /\ w \in Graph

(* Next-state relation *)

Next ==
  /\ v' \in Graph
  /\ w' \in Graph

(* Invariant *)

Inv ==
  /\ v \in Graph
  /\ w \in Graph
  /\ v \in TestGraph
  /\ w \in TestGraph
  /\ Cardinality(BoundedSeqTLCEval(BoundedSeqTLCEval({1,2,3}, 3), 3)) = 65641

(* Specification *)

Spec == Init /\ [][Next]_<<v,w>>

END MODULE