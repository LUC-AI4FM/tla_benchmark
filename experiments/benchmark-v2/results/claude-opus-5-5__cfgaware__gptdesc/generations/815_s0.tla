------------------------------ MODULE MCParReach ------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, vroot, pc, u, toVroot

vars == <<marked, vroot, pc, u, toVroot>>

-----------------------------------------------------------------------------
(* Helper definitions for model checking                                     *)
-----------------------------------------------------------------------------

ConnectedToSomeButNotAll ==
    CHOOSE succ \in [Nodes -> SUBSET Nodes] :
        \A n \in Nodes : Cardinality(succ[n]) = 2

LimitedSeq(S) == UNION {[1..n -> S] : n \in 0..Cardinality(Nodes)}

Seq(S) == LimitedSeq(S)

-----------------------------------------------------------------------------
(* Reachability                                                              *)
-----------------------------------------------------------------------------

Len(s) == Cardinality(DOMAIN s)

IsPathFromTo(p, m, n) ==
    /\ Len(p) > 0
    /\ p[1] = m
    /\ p[Len(p)] = n
    /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in Succ[p[i]]

ReachableFrom(m) ==
    {n \in Nodes : \E p \in Seq(Nodes) : IsPathFromTo(p, m, n)}

Reachable == ReachableFrom(Root)

-----------------------------------------------------------------------------
(* Parallel reachability algorithm                                           *)
-----------------------------------------------------------------------------

Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = [p \in Procs |-> "a"]
    /\ u = [p \in Procs |-> Root]
    /\ toVroot = [p \in Procs |-> {}]

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

Terminating ==
    /\ \A self \in Procs : pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in Procs : p(self)) \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

-----------------------------------------------------------------------------
(* Invariant and refinement                                                  *)
-----------------------------------------------------------------------------

TypeOK ==
    /\ marked \subseteq Nodes
    /\ vroot \subseteq Nodes
    /\ pc \in [Procs -> {"a", "b", "c", "Done"}]
    /\ u \in [Procs -> Nodes]
    /\ toVroot \in [Procs -> SUBSET Nodes]

Inv ==
    /\ TypeOK
    /\ marked \subseteq Reachable
    /\ vroot \subseteq Reachable
    /\ \A q \in Procs : pc[q] \in {"b", "c"} => u[q] \in Reachable
    /\ \A q \in Procs : toVroot[q] \subseteq Reachable

AbstractInit == marked = {}

AbstractNext ==
    /\ marked' \supseteq marked
    /\ marked' \subseteq Reachable

Refines ==
    /\ AbstractInit
    /\ [][AbstractNext]_marked

=============================================================================