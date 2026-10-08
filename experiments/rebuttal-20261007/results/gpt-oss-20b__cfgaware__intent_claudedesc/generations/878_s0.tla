MODULE SpanningTree
IMPORTING SETS

CONSTANTS Nodes, Edges, Root, MaxDist

VARIABLES parent, dist

vars == <<parent, dist>>

(* Helper definitions *)
Neighbors(n) == { m ∈ Nodes : {n,m} ∈ Edges }

Init ==
  /\ parent = [n ∈ Nodes |-> IF n = Root THEN Root ELSE n]
  /\ dist   = [n ∈ Nodes |-> IF n = Root THEN 0 ELSE MaxDist]

Next ==
  ∃i ∈ Nodes :
    ∃j ∈ Neighbors(i) :
      LET d' ∈ {d ∈ Nat : dist[j] + 1 < d /\ d < dist[i]} IN
        /\ parent' = [parent EXCEPT ![i] = j]
        /\ dist'   = [dist EXCEPT ![i] = d']

SelfLoop == UNCHANGED <<parent, dist>>

NextAction == Next \/ SelfLoop

TypeOK ==
  /\ parent ∈ [Nodes → Nodes]
  /\ dist   ∈ [Nodes → Nat]
  /\ MaxDist ∈ Nat
  /\ Root ∈ Nodes
  /\ Edges ⊆ { e ∈ SUBSET[Nodes] : #e = 2 }
  /\ ∀n ∈ Nodes : dist[n] ≤ MaxDist

Safety ==
  ∀n ∈ Nodes :
    (n = Root => (dist[n] = 0 /\ parent[n] = Root)) /\
    (n ≠ Root =>
      ((∃m ∈ Neighbors(n) : dist[m] < dist[n]) =>
          (parent[n] ∈ Neighbors(n) /\ dist[parent[n]] = dist[n]-1))
       /\ ((¬∃m ∈ Neighbors(n) : dist[m] < dist[n]) =>
           (dist[n] = MaxDist /\ parent[n] = n)))

Terminated == ∀n ∈ Nodes : ∀m ∈ Neighbors(n) : dist[n] ≤ dist[m] + 1

Liveness == <> Terminated

Spec ==
  Init
  /\ [][NextAction]_vars
  /\ []TypeOK
  /\ []Safety

===============================================================================