---------------------------- MODULE ParReach ----------------------------
(***************************************************************************)
(* Parallel graph reachability.                                            *)
(*                                                                         *)
(* A set of worker processes concurrently explore a finite directed graph  *)
(* starting from Root.  A shared work set `vroot` holds nodes waiting to   *)
(* be explored, and the shared set `marked` holds nodes already visited.   *)
(*                                                                         *)
(* Each worker repeatedly does the following:                              *)
(*   - takes a node u from vroot;                                          *)
(*   - if u is not yet marked, marks it and copies Succ[u] into its local  *)
(*     set toVroot;                                                        *)
(*   - moves the nodes of toVroot into vroot, one at a time.               *)
(*                                                                         *)
(* A worker terminates when it finds vroot empty.  The algorithm is        *)
(* checked against the sequential definition `Reachable`.                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,      \* finite set of graph nodes
          Succ,       \* Succ[n] is the set of direct successors of node n
          Root,       \* the starting node
          Procs,      \* set of worker process identifiers
          MaxSucc,    \* bound on out-degree (for tractable model checking)
          MaxQueue    \* bound on size of the shared work set

(***************************************************************************)
(* Graphs whose nodes each have at most k successors.                      *)
(***************************************************************************)
GraphsWithMaxSucc(k) ==
    { s \in [Nodes -> SUBSET Nodes] : \A n \in Nodes : Cardinality(s[n]) <= k }

ASSUME /\ IsFiniteSet(Nodes)
       /\ Root \in Nodes
       /\ Procs # {}
       /\ MaxSucc \in Nat
       /\ MaxQueue \in Nat
       /\ Succ \in GraphsWithMaxSucc(MaxSucc)

(***************************************************************************)
(* Sequential definition of reachability.  R[i] is the set of nodes        *)
(* reachable from Root by a path of length at most i.  Every path in a     *)
(* graph with Cardinality(Nodes) nodes is covered by this bound.           *)
(***************************************************************************)
Reachable ==
    LET R[i \in Nat] ==
          IF i = 0 THEN {Root}
          ELSE R[i-1] \cup UNION { Succ[m] : m \in R[i-1] }
    IN  R[Cardinality(Nodes)]

VARIABLES marked,    \* shared set of visited nodes
          vroot,     \* shared work set of nodes waiting to be explored
          u,         \* u[p]: node currently handled by process p
          toVroot,   \* toVroot[p]: successors not yet pushed by process p
          pc         \* control state of each process

vars == << marked, vroot, u, toVroot, pc >>

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

(***************************************************************************)
(* a: take a node from the work set, or terminate if the work set is empty.*)
(***************************************************************************)
a(self) ==
    /\ pc[self] = "a"
    /\ IF vroot # {}
         THEN \E v \in vroot :
                 /\ u' = [u EXCEPT ![self] = v]
                 /\ vroot' = vroot \ {v}
                 /\ pc' = [pc EXCEPT ![self] = "b"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << u, vroot >>
    /\ UNCHANGED << marked, toVroot >>

(***************************************************************************)
(* b: if the node is new, mark it and record its successors.               *)
(***************************************************************************)
b(self) ==
    /\ pc[self] = "b"
    /\ IF u[self] \notin marked
         THEN /\ marked' = marked \cup {u[self]}
              /\ toVroot' = [toVroot EXCEPT ![self] = Succ[u[self]]]
              /\ pc' = [pc EXCEPT ![self] = "c"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
              /\ UNCHANGED << marked, toVroot >>
    /\ UNCHANGED << vroot, u >>

(***************************************************************************)
(* c: push the recorded successors into the shared work set, one at a time.*)
(***************************************************************************)
c(self) ==
    /\ pc[self] = "c"
    /\ IF toVroot[self] # {}
         THEN \E w \in toVroot[self] :
                 /\ vroot' = vroot \cup {w}
                 /\ toVroot' = [toVroot EXCEPT ![self] = toVroot[self] \ {w}]
                 /\ pc' = [pc EXCEPT ![self] = "c"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
              /\ UNCHANGED << vroot, toVroot >>
    /\ UNCHANGED << marked, u >>

proc(self) == a(self) \/ b(self) \/ c(self)

Terminated == \A p \in Procs : pc[p] = "Done"

(* Allows stuttering after termination, so that the final state is not a deadlock. *)
Terminating == Terminated /\ UNCHANGED vars

Next == (\E self \in Procs : proc(self)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))

(***************************************************************************)
(* Model-checking aids                                                     *)
(***************************************************************************)
\* State constraint that bounds the shared work set.
QueueConstraint == Cardinality(vroot) <= MaxQueue

\* State constraint that bounds each process's local pending set.
LocalQueueConstraint == \A p \in Procs : Cardinality(toVroot[p]) <= MaxQueue

\* Example restricted topology: every node has at most one successor.
LimitedConnectivity == Succ \in GraphsWithMaxSucc(1)

(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)
\* Soundness: no false positives.  Pending work is also reachable.
Sound ==
    /\ marked \subseteq Reachable
    /\ vroot \subseteq Reachable
    /\ \A p \in Procs : toVroot[p] \subseteq Reachable

\* Completeness: on termination, the result equals the sequential definition.
Complete == Terminated => (marked = Reachable)

PartialCorrectness == Sound /\ Complete

\* Liveness: the algorithm eventually terminates.
Termination == <>Terminated

\* The final result is equal to the sequential reachability set.
EventuallyCorrect == <>(marked = Reachable)

THEOREM Spec => [](TypeOK /\ Sound /\ Complete)
THEOREM Spec => Termination
=============================================================================