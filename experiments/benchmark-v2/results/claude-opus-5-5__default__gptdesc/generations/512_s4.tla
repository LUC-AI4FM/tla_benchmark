---------------------------- MODULE PathsToRoot ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxNodes

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  LET R == S \cup UNION {Nbrs(n) : n \in S}
  IN  IF R = S THEN S ELSE ReachableFrom(R)

RECURSIVE ReachIn(_)
ReachIn(k) ==
  IF k = 0 THEN {Root}
  ELSE LET R == ReachIn(k - 1)
       IN  R \cup UNION {Nbrs(x) : x \in R}

Distance(n) ==
  CHOOSE k \in 0..MaxNodes :
    /\ n \in ReachIn(k)
    /\ (k = 0 \/ n \notin ReachIn(k - 1))

ASSUME EdgeAssump == \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2
ASSUME RootAssump == Root \in Nodes
ASSUME MaxNodesAssump == MaxNodes \in Nat /\ Cardinality(Nodes) <= MaxNodes
ASSUME ConnectedAssump == ReachableFrom({Root}) = Nodes

Msg == [from : Nodes, depth : 0..MaxNodes]

(***************************************************************************
--algorithm PathsToRoot {
  variables
    msgs   = [n \in Nodes |-> IF n \in Nbrs(Root)
                                THEN {[from |-> Root, depth |-> 0]}
                                ELSE {}],
    depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxNodes],
    parent = [n \in Nodes |-> n];

  fair process (node \in Nodes) {
    a: while (TRUE) {
         await msgs[self] # {};
         with (m \in msgs[self]) {
           if (m.depth + 1 < depth[self]) {
             depth[self]  := m.depth + 1;
             parent[self] := m.from;
             msgs := [x \in Nodes |->
                        IF x = self THEN msgs[self] \ {m}
                        ELSE IF x \in Nbrs(self)
                             THEN msgs[x] \cup {[from |-> self, depth |-> m.depth + 1]}
                             ELSE msgs[x]]
           } else {
             msgs[self] := msgs[self] \ {m}
           }
         }
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES msgs, depth, parent

vars == << msgs, depth, parent >>

ProcSet == Nodes

Init ==
  /\ msgs   = [n \in Nodes |-> IF n \in Nbrs(Root)
                                 THEN {[from |-> Root, depth |-> 0]}
                                 ELSE {}]
  /\ depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxNodes]
  /\ parent = [n \in Nodes |-> n]

node(self) ==
  /\ msgs[self] # {}
  /\ \E m \in msgs[self] :
       IF m.depth + 1 < depth[self]
         THEN /\ depth'  = [depth EXCEPT ![self] = m.depth + 1]
              /\ parent' = [parent EXCEPT ![self] = m.from]
              /\ msgs' = [x \in Nodes |->
                            IF x = self THEN msgs[self] \ {m}
                            ELSE IF x \in Nbrs(self)
                                 THEN msgs[x] \cup {[from |-> self, depth |-> m.depth + 1]}
                                 ELSE msgs[x]]
         ELSE /\ msgs' = [msgs EXCEPT ![self] = msgs[self] \ {m}]
              /\ UNCHANGED << depth, parent >>

Next == \E self \in Nodes : node(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))
\* END TRANSLATION

-----------------------------------------------------------------------------
TypeOK ==
  /\ msgs   \in [Nodes -> SUBSET Msg]
  /\ depth  \in [Nodes -> 0..MaxNodes]
  /\ parent \in [Nodes -> Nodes]

RootInv == depth[Root] = 0 /\ parent[Root] = Root

ParentInv ==
  \A n \in Nodes \ {Root} :
    depth[n] < MaxNodes =>
      /\ parent[n] \in Nbrs(n)
      /\ depth[parent[n]] < depth[n]

DepthLowerBound == \A n \in Nodes : depth[n] >= Distance(n)

MsgInv ==
  \A n \in Nodes : \A m \in msgs[n] :
    /\ m.from \in Nbrs(n)
    /\ depth[m.from] <= m.depth

Termination == <>(\A n \in Nodes : msgs[n] = {})

Correctness == <>[](\A n \in Nodes : depth[n] = Distance(n))
=============================================================================