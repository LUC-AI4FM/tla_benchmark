---- MODULE PathsToRoot ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Nodes, Edges, root, MaxNodes

SetNbrs(n) == {m \in Nodes : {m, n} \in Edges}

RECURSIVE ReachableIn(_, _)
ReachableIn(S, k) ==
  IF k = 0 THEN S
  ELSE LET T == ReachableIn(S, k - 1)
       IN  T \cup {n \in Nodes : \E m \in T : {m, n} \in Edges}

RECURSIVE ReachableSet(_)
ReachableSet(S) ==
  LET T == S \cup {n \in Nodes : \E m \in S : {m, n} \in Edges}
  IN  IF T = S THEN S ELSE ReachableSet(T)

Reachable(n) == n \in ReachableSet({root})

ASSUME EdgesAssump == \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2
ASSUME RootAssump == root \in Nodes
ASSUME MaxNodesAssump == MaxNodes \in Nat /\ Cardinality(Nodes) <= MaxNodes
ASSUME ReachAssump == \A n \in Nodes : Reachable(n)

Msgs == Nodes \X (0..MaxNodes)

Queues == [Nodes -> SUBSET Msgs]

(* --algorithm PathsToRoot
variables
  msgs = [n \in Nodes |-> IF n \in SetNbrs(root) THEN {<<root, 0>>} ELSE {}],
  depth = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes],
  parent = [n \in Nodes |-> n];
fair process node \in Nodes
begin
  a: while TRUE do
       with m \in msgs[self] do
         if m[2] + 1 < depth[self] then
           depth[self] := m[2] + 1;
           parent[self] := m[1];
           msgs := [k \in Nodes |->
                      IF k = self THEN msgs[k] \ {m}
                      ELSE IF k \in SetNbrs(self)
                             THEN msgs[k] \cup {<<self, m[2] + 1>>}
                             ELSE msgs[k]]
         else
           msgs[self] := msgs[self] \ {m}
         end if
       end with
     end while
end process
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES msgs, depth, parent

vars == << msgs, depth, parent >>

ProcSet == Nodes

Init ==
  /\ msgs = [n \in Nodes |-> IF n \in SetNbrs(root) THEN {<<root, 0>>} ELSE {}]
  /\ depth = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
  /\ parent = [n \in Nodes |-> n]

node(self) ==
  \E m \in msgs[self] :
     IF m[2] + 1 < depth[self]
       THEN /\ depth' = [depth EXCEPT ![self] = m[2] + 1]
            /\ parent' = [parent EXCEPT ![self] = m[1]]
            /\ msgs' = [k \in Nodes |->
                          IF k = self THEN msgs[k] \ {m}
                          ELSE IF k \in SetNbrs(self)
                                 THEN msgs[k] \cup {<<self, m[2] + 1>>}
                                 ELSE msgs[k]]
       ELSE /\ msgs' = [msgs EXCEPT ![self] = msgs[self] \ {m}]
            /\ UNCHANGED << depth, parent >>

Next == \E self \in Nodes : node(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))
\* END TRANSLATION

TypeOK ==
  /\ msgs \in Queues
  /\ depth \in [Nodes -> 0..MaxNodes]
  /\ parent \in [Nodes -> Nodes]

====