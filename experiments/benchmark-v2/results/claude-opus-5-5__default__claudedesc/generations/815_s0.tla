------------------------------ MODULE MCParReach ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, n3, n4, p1, p2, Succ

Nodes == {n1, n2, n3, n4}
Root  == n1
Procs == {p1, p2}

ConnectedToSomeButNotAll ==
    {f \in [Nodes -> SUBSET Nodes] : \A n \in Nodes : Cardinality(f[n]) = 2}

ASSUME Succ \in ConnectedToSomeButNotAll

LimitedSeq(S) == UNION {[1..n -> S] : n \in 0..Cardinality(Nodes)}

IsPathFromTo(p, m, n) ==
    /\ Len(p) > 0
    /\ p[1] = m
    /\ p[Len(p)] = n
    /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in Succ[p[i]]

ReachableFrom(m) ==
    {n \in Nodes : \E p \in LimitedSeq(Nodes) : IsPathFromTo(p, m, n)}

Reachable == ReachableFrom(Root)

-----------------------------------------------------------------------------
(* Parallel reachability algorithm (ParReach)                               *)
-----------------------------------------------------------------------------
VARIABLES marked, vroot, u, toVroot, pc

vars == <<marked, vroot, u, toVroot, pc>>

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

Terminating ==
    /\ \A self \in Procs : pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in Procs : p(self)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in Procs : pc[self] = "Done")

-----------------------------------------------------------------------------
(* Safety invariant                                                         *)
-----------------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ vroot \subseteq Nodes
    /\ u \in [Procs -> Nodes]
    /\ toVroot \in [Procs -> SUBSET Nodes]
    /\ pc \in [Procs -> {"a", "b", "c", "Done"}]

Inv ==
    /\ TypeOK
    /\ marked \subseteq Reachable
    /\ vroot \subseteq Reachable
    /\ \A q \in Procs : toVroot[q] \subseteq Reachable
    /\ \A q \in Procs : pc[q] \in {"b", "c"} => u[q] \in Reachable
    /\ (\A q \in Procs : pc[q] = "Done") => (marked = Reachable)

-----------------------------------------------------------------------------
(* Refinement of the sequential reachability algorithm (Reachable)          *)
-----------------------------------------------------------------------------
vrootBar ==
    vroot \cup {u[q] : q \in {r \in Procs : pc[r] \in {"b", "c"}}}
          \cup UNION {toVroot[q] : q \in Procs}

pcBar == IF \A q \in Procs : pc[q] = "Done" THEN "Done" ELSE "a"

RVars == <<marked, vrootBar, pcBar>>

RInit ==
    /\ marked = {}
    /\ vrootBar = {Root}
    /\ pcBar = "a"

RNext ==
    \/ /\ pcBar = "a"
       /\ vrootBar # {}
       /\ \E v \in vrootBar :
            IF v \notin marked
              THEN /\ marked' = marked \cup {v}
                   /\ vrootBar' = vrootBar \cup Succ[v]
              ELSE /\ vrootBar' = vrootBar \ {v}
                   /\ marked' = marked
       /\ pcBar' = "a"
    \/ /\ pcBar = "a"
       /\ vrootBar = {}
       /\ pcBar' = "Done"
       /\ marked' = marked
       /\ vrootBar' = vrootBar

RSpec == RInit /\ [][RNext]_RVars /\ WF_RVars(RNext)

Refines == RSpec

THEOREM Spec => []Inv
THEOREM Spec => Refines
=============================================================================