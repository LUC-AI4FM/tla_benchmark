--------------------------- MODULE RootedTree ---------------------------
EXTENDS Naturals

CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME
  Root \in Nodes
  /\ MaxCardinality \in Nat
  /\ Edges \subseteq Nodes × Nodes

VARIABLES mom, dist

(* Initial state *)
Init ==
   /\ mom = [i \in Nodes |-> i]
   /\ dist = [i \in Nodes |-> IF i = Root THEN 0 ELSE MaxCardinality]

(* Next-state action *)
Next ==
  ∃ v \in Nodes, u \in Nodes, d \in Nat :
     /\ [v,u] \in Edges
     /\ dist[u] < dist[v]
     /\ d >= dist[u]+1
     /\ d < dist[v]
     /\ mom' = [mom EXCEPT ![v] = u]
     /\ dist' = [dist EXCEPT ![v] = d]

(* Termination condition: no node can decrease distance *)
Terminated == ∀ v \in Nodes : ¬∃ u \in Nodes : [v,u] \in Edges /\ dist[u] < dist[v]

(* Correct tree property *)
TreeCorrect ==
   /\ mom[Root] = Root
   /\ dist[Root] = 0
   /\ ∀ v \in Nodes \ {Root} :
          /\ [v, mom[v]] \in Edges
          /\ dist[v] = dist[mom[v]] + 1

(* Safety invariant *)
Inv == Terminated => TreeCorrect

(* Liveness properties *)
LivenessTerm := <> Terminated
LivenessParent := ∀ v \in Nodes : <> (mom[v] = Root)

Spec ==
   Init
   /\ [][Next]_vars
   /\ WF_vars(Next)
   /\ Inv
   /\ LivenessTerm
   /\ LivenessParent

=============================================================================