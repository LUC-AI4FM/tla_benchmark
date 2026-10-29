------------------------- MODULE ParallelReachability -------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Succ, Root, Procs

(* Concrete values used by the model-checking configuration *)
NodesVal == {1, 2, 3, 4, 5}

SuccVal == [n \in NodesVal |->
              CASE n = 1 -> {2, 3}
                [] n = 2 -> {4}
                [] n = 3 -> {1, 2}
                [] n = 4 -> {}
                [] n = 5 -> {4}]

RootVal == 1

ProcsVal == {"p1", "p2"}

ASSUME Root \in Nodes
ASSUME \A n \in Nodes : Succ[n] \subseteq Nodes

(* Set of nodes reachable from a given set, computed as a least fixpoint *)
RECURSIVE ReachSet(_)
ReachSet(S) ==
  LET T == S \cup UNION {Succ[n] : n \in S}
  IN  IF T = S THEN S ELSE ReachSet(T)

Reachable == ReachSet({Root})

VARIABLES
  marked,   \* nodes marked as reachable (shared)
  vroot,    \* nodes still to be explored (shared work pool)
  pc,       \* control state of each process
  u,        \* node currently examined by each process
  toVroot   \* newly discovered successors to be added to the pool

vars == <<marked, vroot, pc, u, toVroot>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ vroot \subseteq Nodes
  /\ pc \in [Procs -> {"a", "b", "c", "Done"}]
  /\ u \in [Procs -> Nodes]
  /\ toVroot \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {}
  /\ vroot = {Root}
  /\ pc = [p \in Procs |-> "a"]
  /\ u = [p \in Procs |-> Root]
  /\ toVroot = [p \in Procs |-> {}]

(* Pick a node from the work pool, or finish if the pool is empty *)
A(p) ==
  /\ pc[p] = "a"
  /\ IF vroot # {}
       THEN \E v \in vroot :
              /\ vroot' = vroot \ {v}
              /\ u' = [u EXCEPT ![p] = v]
              /\ pc' = [pc EXCEPT ![p] = "b"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "Done"]
            /\ UNCHANGED <<vroot, u>>
  /\ UNCHANGED <<marked, toVroot>>

(* Mark the node (if not yet marked) and collect its successors *)
B(p) ==
  /\ pc[p] = "b"
  /\ IF u[p] \notin marked
       THEN /\ marked' = marked \cup {u[p]}
            /\ toVroot' = [toVroot EXCEPT ![p] = Succ[u[p]]]
            /\ pc' = [pc EXCEPT ![p] = "c"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "a"]
            /\ UNCHANGED <<marked, toVroot>>
  /\ UNCHANGED <<vroot, u>>

(* Contribute discovered successors to the shared work pool *)
C(p) ==
  /\ pc[p] = "c"
  /\ vroot' = vroot \cup toVroot[p]
  /\ toVroot' = [toVroot EXCEPT ![p] = {}]
  /\ pc' = [pc EXCEPT ![p] = "a"]
  /\ UNCHANGED <<marked, u>>

proc(p) == A(p) \/ B(p) \/ C(p)

Terminating ==
  /\ \A p \in Procs : pc[p] = "Done"
  /\ UNCHANGED vars

Next == (\E p \in Procs : proc(p)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A p \in Procs : WF_vars(proc(p))

AllDone == \A p \in Procs : pc[p] = "Done"

(* Soundness: only reachable nodes are marked *)
Soundness == marked \subseteq Reachable

(* Completeness and root inclusion upon termination *)
Completeness == AllDone => (marked = Reachable)

RootIncluded == AllDone => (Root \in marked)

Inv ==
  /\ TypeOK
  /\ Soundness
  /\ vroot \subseteq Reachable
  /\ Completeness
  /\ RootIncluded

Termination == <>AllDone

=============================================================================