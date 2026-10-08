------------------------------ MODULE GraphAgents ------------------------------
EXTENDS Sequences

CONSTANTS Graph, TestGraph

VARIABLES agent1Edge, agent2Edge

(* --- Initial state ----------------------------------------------------- *)
Init == /\ agent1Edge ∈ Graph
        /\ agent2Edge ∈ Graph

(* --- Next‑state relation ----------------------------------------------- *)
Next == \E e1 \in Graph, e2 \in Graph :
          /\ agent1Edge' = e1
          /\ agent2Edge' = e2

(* --- Helper definitions ------------------------------------------------- *)
SeqEdges == <<agent1Edge, agent2Edge>>

Inv == /\ agent1Edge ∈ Graph
        /\ agent2Edge ∈ Graph
        /\ agent1Edge ∈ TestGraph
        /\ agent2Edge ∈ TestGraph
        /\ Len(SeqEdges) = 2

(* --- System specification ----------------------------------------------- *)
Spec == Init /\ [][Next]_<<agent1Edge, agent2Edge>>

THEOREM Spec => []Inv
=============================================================================