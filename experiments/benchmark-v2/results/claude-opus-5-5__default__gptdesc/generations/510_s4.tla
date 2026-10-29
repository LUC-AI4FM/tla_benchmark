------------------------------ MODULE Reachable ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Edges, root, MaxNodes

-----------------------------------------------------------------------------
(* Graph operators *)

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

SetNbrs(S) == UNION {Nbrs(n) : n \in S}

(* Declarative definition: the nodes contained in every set of nodes that *)
(* includes S and is closed under taking neighbors.                       *)
ReachableFrom(S) ==
  {n \in Nodes :
     \A T \in SUBSET Nodes :
        ((S \cap Nodes) \subseteq T /\ SetNbrs(T) \subseteq T) => n \in T}

(* Executable recursive definition *)
RECURSIVE RF(_)
RF(S) == LET T == S \cup SetNbrs(S)
         IN  IF T = S THEN S ELSE RF(T)

-----------------------------------------------------------------------------
ASSUME EdgeAssump  == \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
ASSUME RootAssump  == root \in Nodes
ASSUME NodesAssump == MaxNodes \in Nat /\ Cardinality(Nodes) <= MaxNodes
ASSUME ConnAssump  == \A n \in Nodes : n \in ReachableFrom({root})

THEOREM RFEquivReachable ==
  \A S \in SUBSET Nodes : RF(S) = ReachableFrom(S)
PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************
--algorithm SpanningTree {
  variables
    depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes],
    parent = [n \in Nodes |-> n],
    msgs   = [n \in Nodes |-> IF n \in Nbrs(root)
                                 THEN {[d |-> 0, from |-> root]} ELSE {}];
  fair process (node \in Nodes) {
    a: while (TRUE) {
         await msgs[self] # {};
         with (m \in msgs[self]) {
           if (m.d + 1 < depth[self]) {
             depth[self] := m.d + 1;
             parent[self] := m.from;
             msgs := [n \in Nodes |->
                        IF n = self THEN msgs[n] \ {m}
                        ELSE IF n \in Nbrs(self)
                               THEN msgs[n] \cup {[d |-> m.d + 1, from |-> self]}
                               ELSE msgs[n]]
           } else {
             msgs[self] := msgs[self] \ {m}
           }
         }
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES depth, parent, msgs, pc

vars == << depth, parent, msgs, pc >>

ProcSet == Nodes

Msg == [d : 0..MaxNodes, from : Nodes]

Init == /\ depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
        /\ parent = [n \in Nodes |-> n]
        /\ msgs   = [n \in Nodes |-> IF n \in Nbrs(root)
                                       THEN {[d |-> 0, from |-> root]} ELSE {}]
        /\ pc     = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ msgs[self] # {}
           /\ \E m \in msgs[self] :
                IF m.d + 1 < depth[self]
                  THEN /\ depth'  = [depth EXCEPT ![self] = m.d + 1]
                       /\ parent' = [parent EXCEPT ![self] = m.from]
                       /\ msgs' = [n \in Nodes |->
                                    IF n = self THEN msgs[n] \ {m}
                                    ELSE IF n \in Nbrs(self)
                                           THEN msgs[n] \cup {[d |-> m.d + 1, from |-> self]}
                                           ELSE msgs[n]]
                  ELSE /\ msgs' = [msgs EXCEPT ![self] = msgs[self] \ {m}]
                       /\ UNCHANGED << depth, parent >>
           /\ pc' = [pc EXCEPT ![self] = "a"]

node(self) == a(self)

Next == \E self \in Nodes : node(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Properties *)

TypeOK == /\ depth  \in [Nodes -> 0..MaxNodes]
          /\ parent \in [Nodes -> Nodes]
          /\ msgs   \in [Nodes -> SUBSET Msg]
          /\ pc     \in [Nodes -> {"a"}]

RootInv == depth[root] = 0 /\ parent[root] = root

ParentInv ==
  \A n \in Nodes \ {root} :
     depth[n] < MaxNodes => /\ parent[n] \in Nbrs(n)
                            /\ depth[parent[n]] < depth[n]

MsgInv ==
  \A n \in Nodes : \A m \in msgs[n] :
     /\ m.from \in Nbrs(n)
     /\ depth[m.from] <= m.d

Terminated == \A n \in Nodes : msgs[n] = {}

Correct ==
  Terminated =>
    /\ \A n \in Nodes \ {root} :
          /\ depth[n] < MaxNodes
          /\ parent[n] \in Nbrs(n)
          /\ depth[n] = depth[parent[n]] + 1
    /\ \A n \in Nodes : \A m \in Nbrs(n) : depth[n] <= depth[m] + 1

Termination == <>Terminated

StableTermination == <>[]Terminated

THEOREM Spec => [](TypeOK /\ RootInv /\ ParentInv /\ MsgInv /\ Correct)
THEOREM Spec => Termination
=============================================================================