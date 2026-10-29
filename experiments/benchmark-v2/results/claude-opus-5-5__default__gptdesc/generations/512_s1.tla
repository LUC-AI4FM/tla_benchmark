---------------------------- MODULE PathsToRoot ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxNodes

(***************************************************************************)
(* Graph structure                                                         *)
(***************************************************************************)
Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

NbrsOfSet(S) == UNION {Nbrs(n) : n \in S}

(* Recursive definition of the set of nodes reachable from a set S.        *)
RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  LET T == S \cup NbrsOfSet(S)
  IN  IF T = S THEN S ELSE ReachableFrom(T)

(* Recursive definition of the nodes within distance k of the root.        *)
RECURSIVE Ball(_)
Ball(k) == IF k = 0 THEN {Root}
                    ELSE Ball(k-1) \cup NbrsOfSet(Ball(k-1))

(* Recursive definition of reachability via paths of bounded length.       *)
RECURSIVE ReachableIn(_, _, _)
ReachableIn(m, n, k) ==
  \/ m = n
  \/ /\ k > 0
     /\ \E p \in Nbrs(m) : ReachableIn(p, n, k-1)

Reachable(m, n) == ReachableIn(m, n, MaxNodes)

Dist(n) == CHOOSE k \in 0..MaxNodes :
              /\ n \in Ball(k)
              /\ (k = 0 \/ n \notin Ball(k-1))

ASSUME EdgeAssump  == \A e \in Edges : \E m, n \in Nodes : m # n /\ e = {m, n}
ASSUME RootAssump  == Root \in Nodes
ASSUME BoundAssump == /\ MaxNodes \in Nat
                      /\ IsFiniteSet(Nodes)
                      /\ Cardinality(Nodes) <= MaxNodes
ASSUME ConnAssump  == /\ \A n \in Nodes : Reachable(Root, n)
                      /\ ReachableFrom({Root}) = Nodes

(***************************************************************************
--algorithm PathsToRoot {
  variables
    msgs   = [n \in Nodes |-> IF n \in Nbrs(Root)
                                 THEN {[sender |-> Root, depth |-> 0]}
                                 ELSE {}],
    depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxNodes],
    parent = [n \in Nodes |-> n];
  fair process (node \in Nodes) {
    a: while (TRUE) {
         with (m \in msgs[self]) {
           if (m.depth + 1 < depth[self]) {
             depth[self]  := m.depth + 1;
             parent[self] := m.sender;
             msgs := [n \in Nodes |->
                        IF n = self THEN msgs[self] \ {m}
                        ELSE IF n \in Nbrs(self)
                          THEN msgs[n] \cup {[sender |-> self,
                                              depth  |-> m.depth + 1]}
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
VARIABLES msgs, depth, parent

vars == << msgs, depth, parent >>

ProcSet == Nodes

Init ==
  /\ msgs   = [n \in Nodes |-> IF n \in Nbrs(Root)
                                 THEN {[sender |-> Root, depth |-> 0]}
                                 ELSE {}]
  /\ depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxNodes]
  /\ parent = [n \in Nodes |-> n]

node(self) ==
  \E m \in msgs[self] :
     IF m.depth + 1 < depth[self]
       THEN /\ depth'  = [depth  EXCEPT ![self] = m.depth + 1]
            /\ parent' = [parent EXCEPT ![self] = m.sender]
            /\ msgs' = [n \in Nodes |->
                          IF n = self THEN msgs[self] \ {m}
                          ELSE IF n \in Nbrs(self)
                            THEN msgs[n] \cup {[sender |-> self,
                                                depth  |-> m.depth + 1]}
                            ELSE msgs[n]]
       ELSE /\ msgs' = [msgs EXCEPT ![self] = msgs[self] \ {m}]
            /\ UNCHANGED << depth, parent >>

Next == \E self \in Nodes : node(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))
\* END TRANSLATION

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
Msg == [sender : Nodes, depth : 0..MaxNodes]

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

DepthLowerBound == \A n \in Nodes : depth[n] >= Dist(n)

Done == \A n \in Nodes : msgs[n] = {}

Correct ==
  /\ \A n \in Nodes : depth[n] = Dist(n)
  /\ \A n \in Nodes \ {Root} :
        /\ parent[n] \in Nbrs(n)
        /\ Dist(parent[n]) = Dist(n) - 1

Termination == <>Done

Liveness == <>[]Correct

DoneImpliesCorrect == Done => Correct

THEOREM Spec => [](TypeOK /\ RootInv /\ ParentInv /\ DepthLowerBound)
THEOREM Spec => Termination /\ Liveness
=============================================================================