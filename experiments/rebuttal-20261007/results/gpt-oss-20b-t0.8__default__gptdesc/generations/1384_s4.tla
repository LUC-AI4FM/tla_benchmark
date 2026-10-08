MODULE TinyGraphSpec
EXTENDS Naturals, Sequences, TLC

CONSTANTS EdgeSet, NodeSet, N

VARIABLES state1, state2

(* Helper: convert a set to an arbitrary sequence *)
SeqFromSet(s) == << x \in s : TRUE >>

(* Bounded sequence of the first n elements of a set *)
BoundedSeq(s, n) ==
  Subseq( SeqFromSet(s), 0, Min(n, Len(SeqFromSet(s))) )

(* Random (arbitrary) element from a non‑empty set *)
RandomElement(s) == CHOOSE x \in s : TRUE

(* Derived test graph: edges whose first component is strictly less than the second *)
TestGraph ==
  { e \in EdgeSet : TLCEval(e[0] < e[1]) }

NestedBounded ==
  << BoundedSeq(EdgeSet, N), BoundedSeq(NodeSet, N) >>

Assumption == Len(NestedBounded) = 2

Init ==
  /\ state1 \in EdgeSet
  /\ state2 \in EdgeSet
  /\ Assumption

Next ==
  /\ state1' \in EdgeSet
  /\ state2' \in EdgeSet
  /\ state1' = RandomElement(EdgeSet)
  /\ state2' = RandomElement(EdgeSet)

Invariant ==
  /\ state1 \in TestGraph
  /\ state2 \in TestGraph

Spec == Init /\ [][Next]_<<state1, state2>> /\ Invariant

END MODULE