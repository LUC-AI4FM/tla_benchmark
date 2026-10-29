------------------------------- MODULE ParReach -------------------------------
(***************************************************************************)
(* Parallel version of Misra's sequential reachability algorithm.          *)
(* A finite, non-empty set of processes cooperatively compute the set of   *)
(* nodes reachable from Root in a directed graph given by Succ.            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Succ, Root, Procs

ASSUME GraphAssump ==
          /\ IsFiniteSet(Nodes)
          /\ Succ \in [Nodes -> SUBSET Nodes]
          /\ Root \in Nodes

ASSUME ProcsAssump ==
          /\ Procs # {}
          /\ IsFiniteSet(Procs)

(***************************************************************************)
(* Reachable is the smallest set of nodes that contains Root and is closed *)
(* under Succ.                                                             *)
(***************************************************************************)
IsClosed(S) == \A m \in S : Succ[m] \subseteq S

Reachable ==
  {n \in Nodes : \A S \in SUBSET Nodes : (Root \in S /\ IsClosed(S)) => n \in S}

(***************************************************************************)
(* Variables                                                               *)
(*   marked  : shared set of marked (visited) nodes                        *)
(*   vroot   : shared frontier of nodes yet to be explored                 *)
(*   u       : u[p] is the node currently being processed by p             *)
(*   toVroot : toVroot[p] is the set of successors p still has to add      *)
(*   pc      : control state of each process                               *)
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

(* a: while vroot # {} pick a node from the frontier, else terminate *)
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

(* b: if the node is unmarked, mark it and schedule its successors *)
b(self) ==
  /\ pc[self] = "b"
  /\ IF u[self] \notin marked
       THEN /\ marked' = marked \cup {u[self]}
            /\ toVroot' = [toVroot EXCEPT ![self] = Succ[u[self]]]
            /\ pc' = [pc EXCEPT ![self] = "c"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
            /\ UNCHANGED <<marked, toVroot>>
  /\ UNCHANGED <<vroot, u>>

(* c: add the successors to the frontier one at a time *)
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

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

AllDone == \A q \in Procs : pc[q] = "Done"

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)
Safety == marked \subseteq Reachable

PartialCorrectness == AllDone => (marked = Reachable)

Termination == <>AllDone

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to the sequential (Misra) reachability algorithm.    *)
(***************************************************************************)
vrootBar ==
  vroot \cup {u[q] : q \in {r \in Procs : pc[r] = "b"}}
        \cup UNION {toVroot[q] : q \in Procs}

pcBar == IF AllDone THEN "Done" ELSE "a"

(* Sequential algorithm, expressed over the refinement-mapped variables. *)
SeqInit ==
  /\ marked = {}
  /\ vrootBar = {Root}
  /\ pcBar = "a"

SeqNext ==
  \/ /\ pcBar = "a"
     /\ vrootBar # {}
     /\ \E v \in vrootBar :
          IF v \notin marked
            THEN /\ marked' = marked \cup {v}
                 /\ vrootBar' \in { vrootBar \cup Succ[v],
                                    (vrootBar \ {v}) \cup Succ[v] }
            ELSE /\ vrootBar' = vrootBar \ {v}
                 /\ marked' = marked
     /\ pcBar' = "a"
  \/ /\ pcBar = "a"
     /\ vrootBar = {}
     /\ pcBar' = "Done"
     /\ UNCHANGED <<marked, vrootBar>>

seqVars == <<marked, vrootBar, pcBar>>

SeqSpec == SeqInit /\ [][SeqNext]_seqVars /\ WF_seqVars(SeqNext)

Refinement == SeqSpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Inductive invariant relating process-local state to global state.       *)
(***************************************************************************)
Inv ==
  /\ TypeOK
  /\ marked \subseteq Reachable
  /\ vroot \subseteq Reachable
  /\ \A q \in Procs : u[q] \in Reachable
  /\ \A q \in Procs : toVroot[q] \subseteq Reachable
  /\ \A q \in Procs : pc[q] \in {"a", "b", "Done"} => toVroot[q] = {}
  /\ \A q \in Procs : pc[q] = "c" => u[q] \in marked
  /\ \A n \in marked : Succ[n] \subseteq marked \cup vrootBar
  /\ Root \in marked \cup vrootBar
  /\ AllDone => vrootBar = {}

THEOREM Spec => []Inv
THEOREM Spec => []Safety
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination
THEOREM Spec => Refinement
=============================================================================