---------------------------- MODULE ParallelReachability ----------------------------
(***************************************************************************)
(* A model of a parallel graph-marking algorithm. A finite set of worker   *)
(* processes cooperatively compute the set of nodes reachable from Root    *)
(* in a finite directed graph given by the successor function Succ.        *)
(*                                                                         *)
(* The atomic actions are:                                                 *)
(*   Take(p)    : an idle worker removes some pending node for exploring.  *)
(*   Explore(p) : a worker examines one successor of its current node; if  *)
(*                the successor is unmarked it is marked and added to the  *)
(*                pending set (discovery).                                 *)
(*   Finish(p)  : a worker that examined all successors becomes idle.      *)
(* Several workers may examine the same successor node (redundant work),   *)
(* but discovery is atomic, so no node is lost.                            *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANTS Nodes,   \* finite set of graph nodes
          Succ,    \* successor function: Succ[n] is the set of successors of n
          Root,    \* distinguished root node
          Procs    \* finite set of worker processes

ASSUME /\ IsFiniteSet(Nodes)
       /\ IsFiniteSet(Procs)
       /\ Procs # {}
       /\ Root \in Nodes
       /\ Succ \in [Nodes -> SUBSET Nodes]

NoNode == CHOOSE x : x \notin Nodes

VARIABLES marked,    \* set of nodes discovered so far
          pending,   \* set of marked nodes still awaiting exploration
          pc,        \* pc[p] \in {"idle", "explore"}
          current,   \* current[p]: node being explored by p
          toVisit    \* toVisit[p]: successors of current[p] not yet examined by p

vars == <<marked, pending, pc, current, toVisit>>

(***************************************************************************)
(* Reachability: least fixed point of successor closure from Root.         *)
(***************************************************************************)
RECURSIVE ReachFrom(_)
ReachFrom(S) ==
    LET T == S \cup UNION {Succ[n] : n \in S}
    IN  IF T = S THEN S ELSE ReachFrom(T)

Reachable == ReachFrom({Root})

-----------------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ pending \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "explore"}]
    /\ current \in [Procs -> Nodes \cup {NoNode}]
    /\ toVisit \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked  = {Root}
    /\ pending = {Root}
    /\ pc      = [p \in Procs |-> "idle"]
    /\ current = [p \in Procs |-> NoNode]
    /\ toVisit = [p \in Procs |-> {}]

(* An idle worker takes some pending node. *)
Take(p) ==
    /\ pc[p] = "idle"
    /\ \E n \in pending :
         /\ pending' = pending \ {n}
         /\ current' = [current EXCEPT ![p] = n]
         /\ toVisit' = [toVisit EXCEPT ![p] = Succ[n]]
         /\ pc'      = [pc EXCEPT ![p] = "explore"]
    /\ UNCHANGED marked

(* A worker examines one successor; newly discovered nodes are marked and  *)
(* added to the pending set atomically.                                    *)
Explore(p) ==
    /\ pc[p] = "explore"
    /\ \E s \in toVisit[p] :
         /\ toVisit' = [toVisit EXCEPT ![p] = @ \ {s}]
         /\ IF s \notin marked
              THEN /\ marked'  = marked \cup {s}
                   /\ pending' = pending \cup {s}
              ELSE UNCHANGED <<marked, pending>>
    /\ UNCHANGED <<pc, current>>

(* A worker that has examined all successors returns to idle. *)
Finish(p) ==
    /\ pc[p] = "explore"
    /\ toVisit[p] = {}
    /\ pc'      = [pc EXCEPT ![p] = "idle"]
    /\ current' = [current EXCEPT ![p] = NoNode]
    /\ UNCHANGED <<marked, pending, toVisit>>

Quiescent ==
    /\ pending = {}
    /\ \A p \in Procs : pc[p] = "idle"

(* Explicit stuttering once the computation has terminated (no deadlock). *)
Terminated ==
    /\ Quiescent
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Take(p) \/ Explore(p) \/ Finish(p)
    \/ Terminated

Fairness ==
    \A p \in Procs :
        /\ WF_vars(Take(p))
        /\ WF_vars(Explore(p))
        /\ WF_vars(Finish(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
MarkedInNodes == marked \subseteq Nodes

MarkedOnlyReachable == marked \subseteq Reachable

PendingMarked == pending \subseteq marked

(* Inductive invariant explaining why no node is lost: every marked node  *)
(* is pending, being explored, or has all its successors marked.          *)
NoLostNodes ==
    \A n \in marked :
        \/ n \in pending
        \/ \E p \in Procs : /\ pc[p] = "explore"
                            /\ current[p] = n
                            /\ Succ[n] \ toVisit[p] \subseteq marked
        \/ Succ[n] \subseteq marked

(* On quiescence, the marked set is exactly the reachable set. *)
QuiescentCorrect == Quiescent => marked = Reachable

Safety ==
    /\ TypeOK
    /\ MarkedInNodes
    /\ MarkedOnlyReachable
    /\ PendingMarked
    /\ NoLostNodes
    /\ QuiescentCorrect

(* Once marked, a node remains marked. *)
MarkedMonotone == [][marked \subseteq marked']_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
ReachableEventuallyMarked ==
    \A n \in Reachable : <>(n \in marked)

EventuallyQuiescent == <>[]Quiescent

Termination == <>[](Quiescent /\ marked = Reachable)

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => MarkedMonotone
THEOREM Spec => ReachableEventuallyMarked /\ EventuallyQuiescent /\ Termination
=============================================================================