MODULE SpanningTree
EXTENDS Naturals, TLC

CONSTANTS Nodes, Root, Adj

(* Derived constant *)
MaxDist == CARD(Nodes)

VARIABLES dist, parent

TypeInv ==
  /\ dist ∈ [Nodes → Nat]
  /\ parent ∈ [Nodes → Nodes]

Init ==
  /\ TypeInv
  /\ dist = [i ∈ Nodes |-> IF i = Root THEN 0 ELSE MaxDist]
  /\ parent = [i ∈ Nodes |-> i]

Improvement(i,j) == j ∈ Adj[i] /\ dist[j]+1 < dist[i]

Next ==
  ∃i ∈ Nodes :
    ∃j ∈ Nodes :
      Improvement(i,j)
      /\ dist' = [dist EXCEPT ![i] = dist[j]+1]
      /\ parent' = [parent EXCEPT ![i] = j]

NoImprovement == ¬∃i ∈ Nodes : ∃j ∈ Nodes : j ∈ Adj[i] /\ dist[j]+1 < dist[i]

Quiescent == NoImprovement

SafetyInv ==
  ∀i ∈ Nodes :
    IF dist[i] < MaxDist THEN
      /\ parent[i] ∈ Adj[i]
      /\ dist[i] = dist[parent[i]] + 1
    ELSE
      /\ parent[i] = i
      /\ ∀j ∈ Adj[i] : dist[j] = MaxDist

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next) /\ ◇Quiescent

Inv == TypeInv /\ SafetyInv

THEOREM Spec ⇒ []Inv