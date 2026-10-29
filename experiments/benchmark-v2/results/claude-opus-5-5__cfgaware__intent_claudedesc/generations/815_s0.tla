---------------------------- MODULE ParReach ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

ASSUME /\ Root \in Nodes
       /\ Procs # {}

(***************************************************************************)
(* Sequences are represented as functions with domain 1..n.  Seq is        *)
(* defined here (rather than imported) so that it can be overridden by     *)
(* LimitedSeq in the model-checking configuration.                         *)
(***************************************************************************)
Seq(S) == UNION {[1..n -> S] : n \in Nat}

LimitedSeq(S) == UNION {[1..n -> S] : n \in 1..Cardinality(Nodes)}

SeqLen(p) == Cardinality(DOMAIN p)

(***************************************************************************)
(* A graph for model checking: every node has some, but not all, nodes as  *)
(* successors.                                                              *)
(***************************************************************************)
ConnectedToSomeButNotAll ==
  CHOOSE f \in [Nodes -> {S \in SUBSET Nodes : S # {} /\ S # Nodes}] : TRUE

(***************************************************************************)
(* Sequential (mathematical) definition of reachability.                   *)
(***************************************************************************)
IsPathFromTo(p, m, n) ==
  /\ SeqLen(p) > 0
  /\ p[1] = m
  /\ p[SeqLen(p)] = n
  /\ \A i \in 1..(SeqLen(p) - 1) : p[i+1] \in Succ[p[i]]

ExistsPath(m, n) == \E p \in Seq(Nodes) : IsPathFromTo(p, m, n)

Reachable == {n \in Nodes : ExistsPath(Root, n)}

(***************************************************************************)
(* Parallel algorithm.                                                     *)
(***************************************************************************)
VARIABLES marked, vroot, u, toVroot, pc

vars == <<marked, vroot, u, toVroot, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ vroot \subseteq Nodes
  /\ u \in [Procs -> Nodes]
  /\ toVroot \in [Procs -> SUBSET Nodes]
  /\ pc \in [Procs -> {"a", "b", "c", "Done"}]

Init ==
  /\ marked = {}
  /\ vroot = {Root}
  /\ u = [p \in Procs |-> Root]
  /\ toVroot = [p \in Procs |-> {}]
  /\ pc = [p \in Procs |-> "a"]

a(self) ==
  /\ pc[self] = "a"
  /\ IF vroot # {}
       THEN \E v \in vroot :
              /\ u' = [u EXCEPT ![self] = v]
              /\ vroot' = vroot \ {v}
              /\ pc' = [pc EXCEPT ![self] = "b"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED <<u, vroot>>
  /\ UNCHANGED <<marked, toVroot>>

b(self) ==
  /\ pc[self] = "b"
  /\ IF u[self] \notin marked
       THEN /\ marked' = marked \cup {u[self]}
            /\ toVroot' = [toVroot EXCEPT ![self] = Succ[u[self]]]
            /\ pc' = [pc EXCEPT ![self] = "c"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
            /\ UNCHANGED <<marked, toVroot>>
  /\ UNCHANGED <<vroot, u>>

c(self) ==
  /\ pc[self] = "c"
  /\ IF toVroot[self] # {}
       THEN \E w \in toVroot[self] :
              /\ vroot' = vroot \cup {w}
              /\ toVroot' = [toVroot EXCEPT ![self] = toVroot[self] \ {w}]
              /\ pc' = [pc EXCEPT ![self] = "c"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
            /\ UNCHANGED <<vroot, toVroot>>
  /\ UNCHANGED <<marked, u>>

p(self) == a(self) \/ b(self) \/ c(self)

Terminated == \A self \in Procs : pc[self] = "Done"

Terminating == Terminated /\ UNCHANGED vars

Next == (\E self \in Procs : p(self)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

(***************************************************************************)
(* Correctness.                                                            *)
(***************************************************************************)
Inv ==
  /\ TypeOK
  /\ marked \subseteq Reachable
  /\ vroot \subseteq Reachable
  /\ \A self \in Procs : toVroot[self] \subseteq Reachable
  /\ Terminated => (marked = Reachable)

Refines ==
  /\ [](Terminated => (marked = Reachable))
  /\ [](marked \subseteq Reachable)
  /\ <>Terminated
=============================================================================