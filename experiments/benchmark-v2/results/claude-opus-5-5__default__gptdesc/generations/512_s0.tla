------------------------------- MODULE PathsToRoot -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxNodes

(***************************************************************************)
(* Graph structure and recursive definitions of reachability.               *)
(***************************************************************************)
Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

\* The set of nodes reachable from Root in at most k steps.
RECURSIVE ReachIn(_)
ReachIn(k) == IF k = 0
                THEN {Root}
                ELSE ReachIn(k-1) \cup UNION {Nbrs(m) : m \in ReachIn(k-1)}

\* The closure of a set of nodes under the neighbor relation.
RECURSIVE ReachSet(_)
ReachSet(S) == LET T == S \cup UNION {Nbrs(m) : m \in S}
               IN  IF T = S THEN S ELSE ReachSet(T)

ReachableFromRoot == ReachSet({Root})

\* Distance from Root (length of a shortest path).
Distance(n) == CHOOSE k \in 0..MaxNodes :
                  /\ n \in ReachIn(k)
                  /\ (k = 0 \/ n \notin ReachIn(k-1))

ASSUME EdgeAssump  == \A e \in Edges : /\ e \subseteq Nodes
                                       /\ Cardinality(e) = 2
ASSUME RootAssump  == Root \in Nodes
ASSUME MaxAssump   == /\ MaxNodes \in Nat
                      /\ IsFiniteSet(Nodes)
                      /\ Cardinality(Nodes) <= MaxNodes
ASSUME ReachAssump == Nodes = ReachableFromRoot

(***************************************************************************
--algorithm PathsToRoot {
  variables
    depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxNodes],
    parent = [n \in Nodes |-> n],
    msgs   = [n \in Nodes |-> IF n \in Nbrs(Root)
                                THEN {[from |-> Root, d |-> 0]} ELSE {}];
  fair process (p \in Nodes) {
    a: while (TRUE) {
         with (m \in msgs[self]) {
           if (m.d + 1 < depth[self]) {
             depth[self] := m.d + 1;
             parent[self] := m.from;
             msgs := [q \in Nodes |->
                        IF q \in Nbrs(self)
                          THEN (IF q = self THEN msgs[q] \ {m} ELSE msgs[q])
                                 \cup {[from |-> self, d |-> m.d + 1]}
                          ELSE IF q = self THEN msgs[q] \ {m} ELSE msgs[q]]
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

Msg == [from : Nodes, d : 0..MaxNodes]

Init == /\ depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxNodes]
        /\ parent = [n \in Nodes |-> n]
        /\ msgs   = [n \in Nodes |-> IF n \in Nbrs(Root)
                                       THEN {[from |-> Root, d |-> 0]}
                                       ELSE {}]

p(self) ==
  \E m \in msgs[self] :
     IF m.d + 1 < depth[self]
       THEN /\ depth'  = [depth EXCEPT ![self] = m.d + 1]
            /\ parent' = [parent EXCEPT ![self] = m.from]
            /\ msgs'   = [q \in Nodes |->
                            LET base == IF q = self THEN msgs[q] \ {m}
                                                    ELSE msgs[q]
                            IN  IF q \in Nbrs(self)
                                  THEN base \cup {[from |-> self, d |-> m.d + 1]}
                                  ELSE base]
       ELSE /\ msgs' = [msgs EXCEPT ![self] = msgs[self] \ {m}]
            /\ UNCHANGED << depth, parent >>

\* Allow infinite stuttering once no messages remain, to prevent deadlock.
Terminating == /\ \A n \in Nodes : msgs[n] = {}
               /\ UNCHANGED vars

Next == (\E self \in Nodes : p(self)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(p(self))
\* END TRANSLATION

(***************************************************************************)
(* Safety properties.                                                       *)
(***************************************************************************)
TypeOK == /\ depth  \in [Nodes -> 0..MaxNodes]
          /\ parent \in [Nodes -> Nodes]
          /\ msgs   \in [Nodes -> SUBSET Msg]

RootOK == depth[Root] = 0 /\ parent[Root] = Root

DepthLowerBound == \A n \in Nodes : depth[n] >= Distance(n)

ParentOK ==
  \A n \in Nodes \ {Root} :
     depth[n] < MaxNodes =>
        /\ {n, parent[n]} \in Edges
        /\ depth[parent[n]] < depth[n]

MsgsOK == \A n \in Nodes : \A m \in msgs[n] :
             /\ {n, m.from} \in Edges
             /\ depth[m.from] <= m.d

Inv == TypeOK /\ RootOK /\ DepthLowerBound /\ ParentOK /\ MsgsOK

(***************************************************************************)
(* Liveness properties.                                                     *)
(***************************************************************************)
DepthsCorrect == \A n \in Nodes : depth[n] = Distance(n)

ParentsCorrect ==
  \A n \in Nodes \ {Root} : /\ parent[n] \in Nbrs(n)
                            /\ Distance(parent[n]) = Distance(n) - 1

Termination == <>(\A n \in Nodes : msgs[n] = {})

Correctness == <>[](DepthsCorrect /\ ParentsCorrect)

==================================================================================