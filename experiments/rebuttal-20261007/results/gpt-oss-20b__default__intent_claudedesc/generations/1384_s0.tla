MODULE TLCEvalCaching
EXTENDS Naturals, Sequences

(* Node sets *)
Nodes1 == {1, 2}
Nodes2 == {1, 2, 3}

(* All directed graphs over a set of nodes *)
AllGraphs(nodes) == SUBSET (nodes \times nodes)

(* Bounded sequences of elements from S up to length n *)
BoundedSeq(S, n) == { s \in Seq(S) : Len(s) <= n }

VARIABLES edges, testEdges, curEdges

Init ==
    /\ edges      == CHOOSE e \in AllGraphs(Nodes1) : TRUE
    /\ testEdges  == CHOOSE t \in AllGraphs(Nodes1) : TRUE
    /\ curEdges   == edges ∩ testEdges

Next ==
    UNCHANGED <<edges, testEdges, curEdges>>

(* Safety invariants *)
InvCard1 == #BoundedSeq(Nodes1, 2) = 7
InvCard2 == #(BoundedSeq(BoundedSeq(Nodes1, 2), 2)) = 57
InvCard3 == #BoundedSeq(Nodes2, 3) = 40
InvCard4 == #(BoundedSeq(BoundedSeq(Nodes2, 3), 3)) = 65641
InvStableEdges == curEdges \subseteq edges /\ curEdges \subseteq testEdges

Safety == InvCard1 /\ InvCard2 /\ InvCard3 /\ InvCard4 /\ InvStableEdges

Spec == Init /\ [][Next]_<<edges,testEdges,curEdges>> /\ Safety

===============================================================================