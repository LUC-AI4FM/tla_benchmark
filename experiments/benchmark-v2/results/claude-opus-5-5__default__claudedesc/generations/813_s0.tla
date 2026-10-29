------------------------------- MODULE MC_ParReach -------------------------------
(***************************************************************************)
(* Type-annotated wrapper for the ParReach specification.                  *)
(* The original ParReach module stays tool-agnostic. This module adds      *)
(* Apalache type annotations and a concrete model configuration, then      *)
(* imports the algorithm through INSTANCE.                                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

    ------------------------------ MODULE ParReach ------------------------------
    (***********************************************************************)
    (* Parallel algorithm that computes the set of nodes reachable from    *)
    (* Root in a directed graph. Several processes run it concurrently.    *)
    (***********************************************************************)
    EXTENDS Integers, FiniteSets

    CONSTANTS Nodes, Succ, Root, Procs

    VARIABLES marked, vroot, pc, u, toVroot

    vars == << marked, vroot, pc, u, toVroot >>

    RECURSIVE ReachClosure(_)
    ReachClosure(S) ==
        LET T == S \cup UNION { Succ[n] : n \in S }
        IN  IF T = S THEN S ELSE ReachClosure(T)

    Reachable == ReachClosure({Root})

    Init ==
        /\ marked  = {}
        /\ vroot   = {Root}
        /\ pc      = [p \in Procs |-> "a"]
        /\ u       = [p \in Procs |-> Root]
        /\ toVroot = [p \in Procs |-> {}]

    (* Step a: take a node from the frontier, or terminate if it is empty. *)
    a(self) ==
        /\ pc[self] = "a"
        /\ IF vroot # {}
             THEN \E v \in vroot :
                     /\ u'     = [u EXCEPT ![self] = v]
                     /\ vroot' = vroot \ {v}
                     /\ pc'    = [pc EXCEPT ![self] = "b"]
             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << u, vroot >>
        /\ UNCHANGED << marked, toVroot >>

    (* Step b: mark the node if it is new and prepare its successors. *)
    b(self) ==
        /\ pc[self] = "b"
        /\ IF u[self] \notin marked
             THEN /\ marked'  = marked \cup {u[self]}
                  /\ toVroot' = [toVroot EXCEPT ![self] = Succ[u[self]]]
                  /\ pc'      = [pc EXCEPT ![self] = "c"]
             ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
                  /\ UNCHANGED << marked, toVroot >>
        /\ UNCHANGED << vroot, u >>

    (* Step c: move the successors into the frontier one at a time. *)
    c(self) ==
        /\ pc[self] = "c"
        /\ IF toVroot[self] # {}
             THEN \E w \in toVroot[self] :
                     /\ vroot'   = vroot \cup {w}
                     /\ toVroot' = [toVroot EXCEPT ![self] = toVroot[self] \ {w}]
                     /\ pc'      = [pc EXCEPT ![self] = "c"]
             ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
                  /\ UNCHANGED << vroot, toVroot >>
        /\ UNCHANGED << marked, u >>

    proc(self) == a(self) \/ b(self) \/ c(self)

    Terminating ==
        /\ \A self \in Procs : pc[self] = "Done"
        /\ UNCHANGED vars

    Next == (\E self \in Procs : proc(self)) \/ Terminating

    Spec == /\ Init
            /\ [][Next]_vars
            /\ \A self \in Procs : WF_vars(proc(self))

    Termination == <>(\A self \in Procs : pc[self] = "Done")

    TypeOK ==
        /\ marked \subseteq Nodes
        /\ vroot \subseteq Nodes
        /\ pc \in [Procs -> {"a", "b", "c", "Done"}]
        /\ u \in [Procs -> Nodes]
        /\ toVroot \in [Procs -> SUBSET Nodes]

    Inv ==
        /\ TypeOK
        /\ \A p \in Procs : pc[p] = "c" => u[p] \in marked
        /\ (marked \cup vroot \cup UNION { toVroot[p] : p \in Procs })
              \subseteq Reachable
        /\ (\A p \in Procs : pc[p] = "Done") => (marked = Reachable)

    PartialCorrectness ==
        (\A p \in Procs : pc[p] = "Done") => (marked = Reachable)
    =============================================================================