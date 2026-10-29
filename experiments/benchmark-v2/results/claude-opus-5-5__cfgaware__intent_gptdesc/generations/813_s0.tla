---------------------------- MODULE ParallelReachability ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Succ, Root, Procs

(***************************************************************************)
(* Concrete values for the model-checking configuration.                   *)
(***************************************************************************)
NodesVal == {1, 2, 3, 4, 5}

SuccVal == [n \in NodesVal |->
              CASE n = 1 -> {2, 3}
                [] n = 2 -> {3, 1}
                [] n = 3 -> {3}
                [] n = 4 -> {1, 5}
                [] n = 5 -> {}]

RootVal == 1

ProcsVal == {"p1", "p2"}

(***************************************************************************)
(* Reachability in the graph.                                              *)
(***************************************************************************)
ReachN[n \in Nat] ==
    IF n = 0 THEN {Root}
    ELSE ReachN[n-1] \cup UNION {Succ[m] : m \in ReachN[n-1]}

Reachable == ReachN[Cardinality(Nodes)]

(***************************************************************************)
(* State variables.                                                        *)
(*   marked  : nodes discovered so far                                     *)
(*   vroot   : pending nodes whose successors still need exploring         *)
(*   pc      : control state of each worker                                *)
(*   u       : node currently being explored by each worker                *)
(*   toVroot : successors of u still to be examined by each worker         *)
(***************************************************************************)
VARIABLES marked, vroot, pc, u, toVroot

vars == <<marked, vroot, pc, u, toVroot>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ vroot \subseteq Nodes
    /\ pc \in [Procs -> {"a", "b", "Done"}]
    /\ u \in [Procs -> Nodes]
    /\ toVroot \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {Root}
    /\ vroot = {Root}
    /\ pc = [p \in Procs |-> "a"]
    /\ u = [p \in Procs |-> Root]
    /\ toVroot = [p \in Procs |-> {}]

(* Take a pending node (or terminate if none remain). *)
Take(p) ==
    /\ pc[p] = "a"
    /\ IF vroot # {}
         THEN \E n \in vroot :
                /\ vroot' = vroot \ {n}
                /\ u' = [u EXCEPT ![p] = n]
                /\ toVroot' = [toVroot EXCEPT ![p] = Succ[n]]
                /\ pc' = [pc EXCEPT ![p] = "b"]
         ELSE /\ pc' = [pc EXCEPT ![p] = "Done"]
              /\ UNCHANGED <<vroot, u, toVroot>>
    /\ UNCHANGED marked

(* Explore one successor of the current node; add it if newly discovered. *)
Explore(p) ==
    /\ pc[p] = "b"
    /\ IF toVroot[p] # {}
         THEN \E w \in toVroot[p] :
                /\ toVroot' = [toVroot EXCEPT ![p] = @ \ {w}]
                /\ IF w \notin marked
                     THEN /\ marked' = marked \cup {w}
                          /\ vroot' = vroot \cup {w}
                     ELSE UNCHANGED <<marked, vroot>>
                /\ UNCHANGED <<pc, u>>
         ELSE /\ pc' = [pc EXCEPT ![p] = "a"]
              /\ UNCHANGED <<marked, vroot, u, toVroot>>

proc(p) == Take(p) \/ Explore(p)

Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next == (\E p \in Procs : proc(p)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A p \in Procs : WF_vars(proc(p))

(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)
MarkedInNodes == marked \subseteq Nodes

OnlyReachableMarked == marked \subseteq Reachable

PendingAreMarked == vroot \subseteq marked

CorrectAtTermination ==
    (\A p \in Procs : pc[p] = "Done") => (marked = Reachable /\ vroot = {})

Inv ==
    /\ TypeOK
    /\ MarkedInNodes
    /\ OnlyReachableMarked
    /\ PendingAreMarked
    /\ CorrectAtTermination

MarkedMonotone == [][marked \subseteq marked']_vars

(***************************************************************************)
(* Liveness properties.                                                    *)
(***************************************************************************)
Termination == <>(\A p \in Procs : pc[p] = "Done")

Quiescence == <>[](vroot = {} /\ \A p \in Procs : pc[p] = "Done")

AllReachableMarked == \A n \in Reachable : <>(n \in marked)

Completion == <>[](marked = Reachable)

=============================================================================