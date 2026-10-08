------------------------------ MODULE RootedSpanningTree ------------------------------
EXTENDS Naturals, TLC

(*--------------------------------------------------------------------------*)
(* CONSTANTS *)
CONSTANTS Nodes, Edges, Root, Bound

(*--------------------------------------------------------------------------*)
(* VARIABLES *)
VARIABLES parent, dist, msgs

(*--------------------------------------------------------------------------*)
(* Helper definitions *)

Neighbors(n) == { m ∈ Nodes : (<<n,m>> ∈ Edges) }

MsgSet == { <<src,dst,d>> : src∈Nodes /\ dst∈Nodes /\ d∈Nat }

(*--------------------------------------------------------------------------*)
(* TYPE CHECKING *)
TypeOK ==
  /\ Nodes \subseteq Nat
  /\ Edges ⊆ { <<u,v>> : u∈Nodes /\ v∈Nodes /\ u≠v }
  /\ ∀u,v ∈ Nodes :
        (<<u,v>> ∈ Edges) ⇔ (<<v,u>> ∈ Edges)
  /\ Root ∈ Nodes
  /\ Bound ∈ Nat /\ Bound >= #Nodes
  /\ parent ∈ [Nodes -> Nodes]
  /\ dist   ∈ [Nodes -> Nat]
  /\ msgs   ∈ SUBSET MsgSet

(*--------------------------------------------------------------------------*)
(* INITIAL STATE *)
Init ==
  /\ parent = [i ∈ Nodes |-> IF i = Root THEN Root ELSE i]
  /\ dist   = [i ∈ Nodes |-> IF i = Root THEN 0 ELSE Bound]
  /\ msgs   = { <<Root, n, 0>> : n ∈ Neighbors(Root) }

(*--------------------------------------------------------------------------*)
(* ACTIONS *)

Receive ==
  LET m \in msgs
      src == m[1] ; dst == m[2] ; d' == m[3]
      newDist == d' + 1
  IN /\ UNCHANGED <<parent, dist>>
     /\ msgs' = msgs \ {m}
     /\ IF newDist < dist[dst] THEN
          /\ parent' = [parent EXCEPT ![dst] = src]
          /\ dist'   = [dist EXCEPT ![dst] = newDist]
          /\ msgs'  = msgs' ∪ { <<dst, n, newDist>> : n ∈ Neighbors(dst) }
        ELSE
          /\ parent' = parent
          /\ dist'   = dist

Next == Receive

vars == <<parent, dist, msgs>>

(*--------------------------------------------------------------------------*)
(* SPECIFICATION *)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------------*)
(* CORRECTNESS PROPERTIES *)

Safety ==
  ∀i ∈ Nodes :
    IF dist[i] = 0 THEN i = Root
    ELSE IF dist[i] < Bound THEN
      parent[i] ∈ Neighbors(i) /\ dist[parent[i]] + 1 = dist[i]
    ELSE (* dist[i] = Bound *)
      parent[i] = i

Liveness == <> (msgs = ∅ /\ Safety)

=============================================================================