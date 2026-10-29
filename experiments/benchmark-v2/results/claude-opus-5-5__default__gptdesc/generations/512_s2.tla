---- MODULE PathsToRoot ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Edges, Root, MaxNodes

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

RECURSIVE ReachIn(_, _)
ReachIn(S, k) ==
  IF k = 0 THEN S
  ELSE ReachIn(S \cup UNION {Nbrs(n) : n \in S}, k - 1)

Reachable(n) == ReachIn({n}, MaxNodes)

ReachableFrom[S \in SUBSET Nodes] ==
  LET Next1 == S \cup UNION {Nbrs(n) : n \in S}
  IN  IF Next1 = S THEN S ELSE ReachableFrom[Next1]

ReachableTo(n) == ReachableFrom[{n}]

ASSUME EdgesAssump ==
  \A e \in Edges : /\ e \subseteq Nodes
                   /\ Cardinality(e) = 2

ASSUME RootAssump == Root \in Nodes

ASSUME MaxNodesAssump ==
  /\ MaxNodes \in Nat
  /\ IsFiniteSet(Nodes)
  /\ Cardinality(Nodes) <= MaxNodes

ASSUME ConnectedAssump == \A n \in Nodes : n \in Reachable(Root)

NoParent == CHOOSE x : x \notin Nodes

(***************************************************************************
--algorithm PathsToRoot {
  variables
    msgs   = [n \in Nodes |-> IF n \in Nbrs(Root) THEN {<<Root, 0>>} ELSE {}],
    depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxNodes],
    parent = [n \in Nodes |-> IF n = Root THEN Root ELSE NoParent];
  fair process (node \in Nodes) {
    a: while (TRUE) {
         with (msg \in msgs[self]) {
           if (msg[2] + 1 < depth[self]) {
             depth[self] := msg[2] + 1;
             parent[self] := msg[1];
             msgs := [m \in Nodes |->
                        IF m = self THEN msgs[self] \ {msg}
                        ELSE IF m \in Nbrs(self)
                               THEN msgs[m] \cup {<<self, msg[2] + 1>>}
                               ELSE msgs[m]]
           } else {
             msgs[self] := msgs[self] \ {msg}
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
  /\ msgs = [n \in Nodes |-> IF n \in Nbrs(Root) THEN {<<Root, 0>>} ELSE {}]
  /\ depth = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxNodes]
  /\ parent = [n \in Nodes |-> IF n = Root THEN Root ELSE NoParent]

node(self) ==
  \E msg \in msgs[self] :
    IF msg[2] + 1 < depth[self]
      THEN /\ depth' = [depth EXCEPT ![self] = msg[2] + 1]
           /\ parent' = [parent EXCEPT ![self] = msg[1]]
           /\ msgs' = [m \in Nodes |->
                         IF m = self THEN msgs[self] \ {msg}
                         ELSE IF m \in Nbrs(self)
                                THEN msgs[m] \cup {<<self, msg[2] + 1>>}
                                ELSE msgs[m]]
      ELSE /\ msgs' = [msgs EXCEPT ![self] = msgs[self] \ {msg}]
           /\ UNCHANGED << depth, parent >>

Terminated == \A n \in Nodes : msgs[n] = {}

Next == (\E self \in Nodes : node(self))
        \/ (Terminated /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))
\* END TRANSLATION

TypeOK ==
  /\ msgs \in [Nodes -> SUBSET (Nodes \X (0..MaxNodes))]
  /\ depth \in [Nodes -> 0..MaxNodes]
  /\ parent \in [Nodes -> Nodes \cup {NoParent}]

RootInv == depth[Root] = 0 /\ parent[Root] = Root

ParentInv ==
  \A n \in Nodes \ {Root} :
    parent[n] # NoParent =>
      /\ parent[n] \in Nbrs(n)
      /\ depth[n] >= depth[parent[n]] + 1

NoParentInv ==
  \A n \in Nodes \ {Root} : (parent[n] = NoParent) <=> (depth[n] = MaxNodes)

Done ==
  /\ \A n \in Nodes : parent[n] \in Nodes
  /\ \A n \in Nodes : depth[n] < MaxNodes

Termination == <>Terminated

Liveness == <>[]Done
====