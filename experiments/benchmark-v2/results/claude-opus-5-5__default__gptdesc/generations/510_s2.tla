------------------------------- MODULE SpanningPaths -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, root, MaxNodes

-----------------------------------------------------------------------------
(***************************************************************************)
(* Graph operators                                                         *)
(***************************************************************************)
Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

SetNbrs(S) == UNION {Nbrs(n) : n \in S}

(* Declarative definition: the smallest set of nodes that contains S and  *)
(* is closed under taking neighbors.                                      *)
ReachableFrom(S) ==
  INTER {T \in SUBSET Nodes : S \subseteq T /\ SetNbrs(T) \subseteq T}

(* Executable recursive reachability procedure.                           *)
RECURSIVE RFRec(_, _)
RFRec(Expl, Front) ==
  LET NewFront == SetNbrs(Front) \ (Expl \cup Front)
  IN  IF NewFront = {}
        THEN Expl \cup Front
        ELSE RFRec(Expl \cup Front, NewFront)

RF(S) == RFRec({}, S)

(* Nodes at distance at most k from root.                                 *)
RECURSIVE Ball(_)
Ball(k) == IF k = 0 THEN {root}
                    ELSE Ball(k-1) \cup SetNbrs(Ball(k-1))

Dist(n) == CHOOSE k \in 0..MaxNodes :
              /\ n \in Ball(k)
              /\ \A j \in 0..(k-1) : n \notin Ball(j)

-----------------------------------------------------------------------------
ASSUME EdgeAssump  == \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2
ASSUME RootAssump  == root \in Nodes
ASSUME MaxAssump   == MaxNodes \in Nat /\ Cardinality(Nodes) <= MaxNodes
ASSUME ReachAssump == \A n \in Nodes : n \in ReachableFrom({root})

THEOREM RFCorrect == \A S \in SUBSET Nodes : RF(S) = ReachableFrom(S)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Distributed algorithm: each node process receives depth messages from  *)
(* its neighbors; if a neighbor offers a shorter path to root, the node   *)
(* adopts it as parent, updates its depth and informs its neighbors.      *)
(***************************************************************************)
VARIABLES depth, parent, msgs

vars == <<depth, parent, msgs>>

Msg == [from : Nodes, to : Nodes, d : 0..MaxNodes]

TypeOK ==
  /\ depth  \in [Nodes -> 0..MaxNodes]
  /\ parent \in [Nodes -> Nodes]
  /\ msgs   \subseteq Msg

Init ==
  /\ depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
  /\ parent = [n \in Nodes |-> n]
  /\ msgs   = {[from |-> root, to |-> m, d |-> 0] : m \in Nbrs(root)}

Proc(self) ==
  \E m \in msgs :
     /\ m.to = self
     /\ IF m.d + 1 < depth[self]
          THEN /\ depth'  = [depth  EXCEPT ![self] = m.d + 1]
               /\ parent' = [parent EXCEPT ![self] = m.from]
               /\ msgs'   = (msgs \ {m}) \cup
                              {[from |-> self, to |-> q, d |-> m.d + 1] :
                                  q \in Nbrs(self)}
          ELSE /\ msgs' = msgs \ {m}
               /\ UNCHANGED <<depth, parent>>

Terminated == msgs = {} /\ UNCHANGED vars

Next == (\E self \in Nodes : Proc(self)) \/ Terminated

Spec == Init /\ [][Next]_vars /\ \A self \in Nodes : WF_vars(Proc(self))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety                                                                  *)
(***************************************************************************)
RootInv == depth[root] = 0 /\ parent[root] = root

ParentInv ==
  \A n \in Nodes \ {root} :
     depth[n] < MaxNodes =>
        /\ parent[n] \in Nbrs(n)
        /\ depth[parent[n]] < depth[n]

DepthBound == \A n \in Nodes : depth[n] >= Dist(n)

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
Termination == <>(msgs = {})

Correct ==
  <>[] (\A n \in Nodes :
          /\ depth[n] = Dist(n)
          /\ n # root => parent[n] \in Nbrs(n)
                         /\ depth[parent[n]] = depth[n] - 1)

THEOREM Spec => [](TypeOK /\ RootInv /\ ParentInv /\ DepthBound)
THEOREM Spec => Termination /\ Correct
=============================================================================