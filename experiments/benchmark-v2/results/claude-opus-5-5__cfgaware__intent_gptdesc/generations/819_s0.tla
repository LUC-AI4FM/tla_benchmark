---------------------------- MODULE ParReach ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Root, Procs

ASSUME ProcsAssump == Procs # {}

-----------------------------------------------------------------------------
(* The finite directed graph. *)
Nodes == 1..5

Succ == [n \in Nodes |->
           CASE n = 1 -> {2, 3}
             [] n = 2 -> {4}
             [] n = 3 -> {2, 4}
             [] n = 4 -> {1}
             [] n = 5 -> {1}]

ASSUME RootAssump == Root \in Nodes

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  LET R == S \cup UNION {Succ[n] : n \in S}
  IN  IF R = S THEN S ELSE ReachableFrom(R)

Reachable == ReachableFrom({Root})

-----------------------------------------------------------------------------
VARIABLES marked, vroot, pc, u, toVroot

vars == << marked, vroot, pc, u, toVroot >>

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ u = [p \in Procs |-> Root]
        /\ toVroot = [p \in Procs |-> {}]
        /\ pc = [p \in Procs |-> "a"]

(* Pick a node from the shared pool, or finish if the pool is empty. *)
a(self) == /\ pc[self] = "a"
           /\ IF vroot # {}
                THEN \E v \in vroot :
                       /\ u' = [u EXCEPT ![self] = v]
                       /\ vroot' = vroot \ {v}
                       /\ pc' = [pc EXCEPT ![self] = "b"]
                ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << u, vroot >>
           /\ UNCHANGED << marked, toVroot >>

(* Mark the picked node visited and collect its successors. *)
b(self) == /\ pc[self] = "b"
           /\ IF u[self] \notin marked
                THEN /\ marked' = marked \cup {u[self]}
                     /\ toVroot' = [toVroot EXCEPT ![self] = Succ[u[self]]]
                     /\ pc' = [pc EXCEPT ![self] = "c"]
                ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
                     /\ UNCHANGED << marked, toVroot >>
           /\ UNCHANGED << vroot, u >>

(* Add the successors to the shared pool one at a time. *)
c(self) == /\ pc[self] = "c"
           /\ IF toVroot[self] # {}
                THEN \E w \in toVroot[self] :
                       /\ vroot' = vroot \cup {w}
                       /\ toVroot' = [toVroot EXCEPT ![self] = toVroot[self] \ {w}]
                       /\ pc' = [pc EXCEPT ![self] = "c"]
                ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
                     /\ UNCHANGED << vroot, toVroot >>
           /\ UNCHANGED << marked, u >>

p(self) == a(self) \/ b(self) \/ c(self)

Terminating == /\ \A self \in Procs : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs : p(self)) \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in Procs : pc[self] = "Done")

-----------------------------------------------------------------------------
(* Typing and inductive invariant. *)
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ u \in [Procs -> Nodes]
          /\ toVroot \in [Procs -> SUBSET Nodes]
          /\ pc \in [Procs -> {"a", "b", "c", "Done"}]

Inv == /\ TypeOK
       /\ \A q \in Procs : pc[q] \in {"b", "c"} => u[q] \in Reachable
       /\ \A q \in Procs : pc[q] = "c" => /\ u[q] \in marked
                                          /\ toVroot[q] \subseteq Succ[u[q]]
       /\ \A q \in Procs : toVroot[q] \subseteq Reachable
       /\ marked \cup vroot \subseteq Reachable

Safety == /\ marked \subseteq Nodes
          /\ vroot \subseteq Nodes
          /\ marked \cup vroot \subseteq Reachable

PartialCorrectness ==
  (\A q \in Procs : pc[q] = "Done") => (marked = Reachable)

-----------------------------------------------------------------------------
(* Refinement: abstract sequential algorithm adding a node and all its
   successors atomically. Pending successors of in-progress workers are
   treated as already in the abstract pool. *)
vrootBar == vroot \cup UNION {toVroot[q] : q \in Procs}
             \cup {u[q] : q \in {r \in Procs : pc[r] = "b"}}
pcBar == IF \A q \in Procs : pc[q] = "Done" THEN "Done" ELSE "a"

AbsInit == /\ marked = {}
           /\ vrootBar = {Root}

AbsNext ==
  \/ \E v \in vrootBar :
       IF v \notin marked
         THEN /\ marked' = marked \cup {v}
              /\ vrootBar' = (vrootBar \ {v}) \cup Succ[v]
         ELSE /\ vrootBar' = vrootBar \ {v}
              /\ UNCHANGED marked
  \/ UNCHANGED << marked, vrootBar >>
=============================================================================