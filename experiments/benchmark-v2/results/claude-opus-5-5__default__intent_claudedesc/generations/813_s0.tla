---------------------------- MODULE ParallelReachability ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,   \* the set of nodes of the graph
          Succ,    \* Succ[n] is the set of successors of node n
          Root,    \* the root node
          Procs    \* the set of worker processes

ASSUME /\ IsFiniteSet(Nodes)
       /\ Succ \in [Nodes -> SUBSET Nodes]
       /\ Root \in Nodes
       /\ Procs # {}

-----------------------------------------------------------------------------
(* The set of nodes reachable from a set S by following zero or more edges. *)
RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
    LET R == S \cup UNION {Succ[n] : n \in S}
    IN  IF R = S THEN S ELSE ReachableFrom(R)

Reachable == ReachableFrom({Root})

-----------------------------------------------------------------------------
VARIABLES marked,   \* shared: nodes marked as reachable
          vroot,    \* shared: nodes discovered but not yet examined (work pool)
          pc,       \* control state of each process
          u,        \* node currently examined by each process
          toVroot   \* successors of u that a process still has to add to vroot

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

(* Step a: pick an unexplored node from the shared pool, or terminate. *)
a(p) ==
    /\ pc[p] = "a"
    /\ IF vroot # {}
         THEN \E v \in vroot :
                /\ u' = [u EXCEPT ![p] = v]
                /\ vroot' = vroot \ {v}
                /\ pc' = [pc EXCEPT ![p] = "b"]
         ELSE /\ pc' = [pc EXCEPT ![p] = "Done"]
              /\ UNCHANGED <<u, vroot>>
    /\ UNCHANGED <<marked, toVroot>>

(* Step b: mark the node if it is not yet marked and collect its successors. *)
b(p) ==
    /\ pc[p] = "b"
    /\ IF u[p] \notin marked
         THEN /\ marked' = marked \cup {u[p]}
              /\ toVroot' = [toVroot EXCEPT ![p] = Succ[u[p]]]
              /\ pc' = [pc EXCEPT ![p] = "c"]
         ELSE /\ pc' = [pc EXCEPT ![p] = "a"]
              /\ UNCHANGED <<marked, toVroot>>
    /\ UNCHANGED <<vroot, u>>

(* Step c: contribute newly discovered successors, one at a time, to the pool. *)
c(p) ==
    /\ pc[p] = "c"
    /\ IF toVroot[p] # {}
         THEN \E w \in toVroot[p] :
                /\ vroot' = vroot \cup {w}
                /\ toVroot' = [toVroot EXCEPT ![p] = toVroot[p] \ {w}]
                /\ pc' = [pc EXCEPT ![p] = "c"]
         ELSE /\ pc' = [pc EXCEPT ![p] = "a"]
              /\ UNCHANGED <<vroot, toVroot>>
    /\ UNCHANGED <<marked, u>>

proc(p) == a(p) \/ b(p) \/ c(p)

Terminated == \A p \in Procs : pc[p] = "Done"

(* Stuttering after termination to avoid deadlock reports. *)
Terminating == Terminated /\ UNCHANGED vars

Next == (\E p \in Procs : proc(p)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in Procs : WF_vars(proc(p))

-----------------------------------------------------------------------------
(* Safety properties *)

\* Soundness: only reachable nodes are ever marked.
Soundness == marked \subseteq Reachable

\* Completeness: upon termination every reachable node is marked.
Completeness == Terminated => (marked = Reachable)

\* Root inclusion: the root is marked upon termination, and before that it is
\* either already marked or still awaiting examination.
RootInclusion ==
    /\ Terminated => Root \in marked
    /\ Root \in marked \/ Root \in vroot \/ \E p \in Procs : u[p] = Root /\ pc[p] = "b"

\* Upon termination no work remains.
NoWorkLeft == Terminated => (vroot = {} /\ \A p \in Procs : toVroot[p] = {})

Correctness == Terminated => (marked = Reachable)

(* Liveness properties *)

\* The algorithm eventually terminates.
Termination == <>Terminated

\* Eventually the marked set equals exactly the set of reachable nodes, and stays so.
EventuallyComplete == <>[](marked = Reachable)

THEOREM Spec => [](TypeOK /\ Soundness /\ Completeness /\ RootInclusion /\ NoWorkLeft)
THEOREM Spec => Termination /\ EventuallyComplete
=============================================================================