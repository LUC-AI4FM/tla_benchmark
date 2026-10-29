------------------------------ MODULE ParReach ------------------------------
(***************************************************************************)
(* A concurrent graph reachability algorithm. A fixed finite set of        *)
(* worker processes computes the set of nodes reachable from Root in a     *)
(* finite directed graph.                                                  *)
(*                                                                         *)
(* Shared state:                                                           *)
(*   marked  - the set of visited nodes                                    *)
(*   vroot   - the shared pool of nodes still to be explored               *)
(* Worker-local state:                                                     *)
(*   pc[p]      - control location of worker p                             *)
(*   u[p]       - the node worker p has picked from the pool               *)
(*   toVroot[p] - successors of u[p] that p has not yet added to the pool  *)
(*                                                                         *)
(* Worker p repeatedly does the following:                                 *)
(*   a: if the pool is empty, terminate; else remove some node from it     *)
(*      and put it in u[p].                                                *)
(*   b: if u[p] is not yet visited, mark it and remember its successors.   *)
(*   c: add the remembered successors to the pool, one at a time.          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,   \* the nodes of the graph
          Succ,    \* Succ[n] is the set of successors of node n
          Root,    \* the designated root node
          Procs    \* the set of worker processes

ASSUME GraphAssumption ==
         /\ IsFiniteSet(Nodes)
         /\ Succ \in [Nodes -> SUBSET Nodes]
         /\ Root \in Nodes

ASSUME ProcsAssumption ==
         /\ IsFiniteSet(Procs)
         /\ Procs # {}

NoNode == CHOOSE x : x \notin Nodes

(***************************************************************************)
(* The set of nodes reachable from Root. Reach[n] is the set of nodes      *)
(* reachable by a path of length at most n; since Nodes is finite, paths   *)
(* of length Cardinality(Nodes) suffice.                                   *)
(***************************************************************************)
Reach[n \in Nat] ==
  IF n = 0 THEN {Root}
           ELSE LET P == Reach[n-1]
                IN  P \cup UNION {Succ[x] : x \in P}

Reachable == Reach[Cardinality(Nodes)]

-----------------------------------------------------------------------------
VARIABLES marked, vroot, pc, u, toVroot

vars == <<marked, vroot, pc, u, toVroot>>

Init == /\ marked  = {}
        /\ vroot   = {Root}
        /\ pc      = [p \in Procs |-> "a"]
        /\ u       = [p \in Procs |-> NoNode]
        /\ toVroot = [p \in Procs |-> {}]

(* a: pick an unexplored node from the shared pool, or terminate *)
a(self) == /\ pc[self] = "a"
           /\ IF vroot # {}
                THEN \E v \in vroot :
                        /\ u'     = [u EXCEPT ![self] = v]
                        /\ vroot' = vroot \ {v}
                        /\ pc'    = [pc EXCEPT ![self] = "b"]
                ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED <<u, vroot>>
           /\ UNCHANGED <<marked, toVroot>>

(* b: visit the picked node if it has not been visited *)
b(self) == /\ pc[self] = "b"
           /\ IF u[self] \notin marked
                THEN /\ marked'  = marked \cup {u[self]}
                     /\ toVroot' = [toVroot EXCEPT ![self] = Succ[u[self]]]
                     /\ pc'      = [pc EXCEPT ![self] = "c"]
                ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
                     /\ UNCHANGED <<marked, toVroot>>
           /\ UNCHANGED <<vroot, u>>

(* c: add the successors to the shared pool, one at a time *)
c(self) == /\ pc[self] = "c"
           /\ IF toVroot[self] # {}
                THEN \E w \in toVroot[self] :
                        /\ vroot'   = vroot \cup {w}
                        /\ toVroot' = [toVroot EXCEPT ![self] = toVroot[self] \ {w}]
                        /\ pc'      = [pc EXCEPT ![self] = "c"]
                ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
                     /\ UNCHANGED <<vroot, toVroot>>
           /\ UNCHANGED <<marked, u>>

p(self) == a(self) \/ b(self) \/ c(self)

Terminating == /\ \A self \in Procs : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs : p(self)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

AllDone == \A self \in Procs : pc[self] = "Done"

-----------------------------------------------------------------------------
(***************************************************************************)
(* Typing and simple worker-local invariants.                              *)
(***************************************************************************)
TypeOK == /\ marked  \in SUBSET Nodes
          /\ vroot   \in SUBSET Nodes
          /\ pc      \in [Procs -> {"a", "b", "c", "Done"}]
          /\ u       \in [Procs -> Nodes \cup {NoNode}]
          /\ toVroot \in [Procs -> SUBSET Nodes]
          /\ \A q \in Procs : pc[q] \in {"b", "c"} => u[q] \in Nodes

LocalInv == \A q \in Procs :
              /\ pc[q] = "c" => /\ u[q] \in marked
                                /\ toVroot[q] \subseteq Succ[u[q]]
              /\ pc[q] # "c" => toVroot[q] = {}

(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)
MarkedInGraph == marked \subseteq Nodes
PoolInGraph   == vroot \subseteq Nodes
SafetyInv     == (marked \cup vroot) \subseteq Reachable

(* Stronger local reachability facts *)
LocalReachInv == \A q \in Procs :
                   /\ pc[q] \in {"b", "c"} => u[q] \in Reachable
                   /\ toVroot[q] \subseteq Reachable

(***************************************************************************)
(* Partial correctness: on termination, marked is exactly Reachable.       *)
(***************************************************************************)
PartialCorrectness == AllDone => (marked = Reachable)

(***************************************************************************)
(* Refinement mapping: the pool of the abstract algorithm contains the     *)
(* concrete pool, the nodes currently picked by workers (at b or c), and  *)
(* the successors not yet added by workers at c.                           *)
(***************************************************************************)
vrootBar == vroot
            \cup {u[q] : q \in {r \in Procs : pc[r] \in {"b", "c"}}}
            \cup UNION {toVroot[q] : q \in {r \in Procs : pc[r] = "c"}}

(* Inductive invariant supporting partial correctness and refinement *)
ClosureInv ==
  /\ Root \in marked \cup vrootBar
  /\ \A n \in marked \ {u[q] : q \in {r \in Procs : pc[r] = "c"}} :
        Succ[n] \subseteq marked \cup vrootBar
  /\ \A q \in Procs :
        pc[q] = "c" => Succ[u[q]] \subseteq marked \cup vrootBar
  /\ AllDone => vroot = {}

Inv == /\ TypeOK
       /\ LocalInv
       /\ MarkedInGraph
       /\ PoolInGraph
       /\ SafetyInv
       /\ LocalReachInv
       /\ ClosureInv

(***************************************************************************)
(* Abstract sequential reachability algorithm, expressed over marked and  *)
(* the refinement-mapped pool vrootBar. A node and all its successors are  *)
(* added atomically.                                                       *)
(***************************************************************************)
AbsInit == /\ marked = {}
           /\ vrootBar = {Root}

AbsNext == \E v \in vrootBar :
             IF v \notin marked
               THEN /\ marked'   = marked \cup {v}
                    /\ vrootBar' = vrootBar \cup Succ[v]
               ELSE /\ vrootBar' = vrootBar \ {v}
                    /\ UNCHANGED marked

AbsSpec == /\ AbsInit
           /\ [][AbsNext]_<<marked, vrootBar>>
           /\ WF_<<marked, vrootBar>>(AbsNext)

Refinement == AbsSpec

(***************************************************************************)
(* Liveness. Because Nodes is finite, Reachable is finite, and under weak  *)
(* fairness of every worker the algorithm terminates: all workers become   *)
(* quiescent (Done). Termination occurs iff Reachable is finite, which is  *)
(* guaranteed here by GraphAssumption.                                     *)
(***************************************************************************)
Termination == IsFiniteSet(Reachable) => <>AllDone

Quiescence == <>[]AllDone

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []LocalInv
THEOREM Spec => [](MarkedInGraph /\ PoolInGraph /\ SafetyInv)
THEOREM Spec => []Inv
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination
THEOREM Spec => Refinement
=============================================================================