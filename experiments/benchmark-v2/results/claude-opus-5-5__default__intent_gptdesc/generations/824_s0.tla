------------------------------- MODULE Reachable -------------------------------
(***************************************************************************)
(* Computes the set of nodes reachable from a designated root Root in a    *)
(* directed graph with node set Nodes and successor function Succ.         *)
(*                                                                         *)
(*   marked : nodes already acknowledged as discovered                     *)
(*   vroot  : pending nodes still to be processed                          *)
(*   pc     : control state; "a" while running, "Done" once terminated     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,   \* the set of nodes of the graph
          Succ,    \* Succ[n] is the set of immediate successors of node n
          Root     \* the designated root node

ASSUME ConstantsOK ==
         /\ Root \in Nodes
         /\ Succ \in [Nodes -> SUBSET Nodes]

(***************************************************************************)
(* ReachableFrom(S) is the set of nodes reachable from the nodes in S      *)
(* (including the nodes of S themselves). It is the least superset of S    *)
(* that is closed under Succ. It is computed as a fixpoint, which is       *)
(* well defined when Nodes is finite.                                      *)
(***************************************************************************)
RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  LET T == S \cup UNION {Succ[n] : n \in S}
  IN  IF T = S THEN S ELSE ReachableFrom(T)

Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

vars == <<marked, vroot, pc>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial state: nothing acknowledged, only the root pending.             *)
(***************************************************************************)
Init == /\ marked = {}
        /\ vroot  = {Root}
        /\ pc     = "a"

(***************************************************************************)
(* Processing step: choose a pending node v.                               *)
(*   (a) if v is not yet acknowledged, acknowledge it and add its          *)
(*       immediate successors to the pending set;                          *)
(*   (b) otherwise remove it from the pending set.                         *)
(***************************************************************************)
Process ==
  /\ pc = "a"
  /\ vroot # {}
  /\ \E v \in vroot :
        IF v \notin marked
          THEN /\ marked' = marked \cup {v}
               /\ vroot'  = vroot \cup Succ[v]
          ELSE /\ vroot'  = vroot \ {v}
               /\ UNCHANGED marked
  /\ pc' = "a"

(***************************************************************************)
(* Explicit termination: when the pending set is empty, move to "Done".    *)
(***************************************************************************)
Finish ==
  /\ pc = "a"
  /\ vroot = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, vroot>>

(***************************************************************************)
(* Once terminated, the system only stutters (avoids spurious deadlock).   *)
(***************************************************************************)
Terminated ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Step == Process \/ Finish

Next == Step \/ Terminated

(***************************************************************************)
(* Weak fairness of the processing step (including the final transition   *)
(* to "Done") ensures progress whenever a step is continuously enabled.   *)
(***************************************************************************)
Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Process)
        /\ WF_vars(Finish)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot  \in SUBSET Nodes
          /\ pc     \in {"a", "Done"}

(***************************************************************************)
(* Every successor of an acknowledged node is acknowledged or pending.     *)
(***************************************************************************)
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(***************************************************************************)
(* The acknowledged nodes together with the nodes reachable from the       *)
(* pending set equal the nodes reachable from acknowledged \cup pending.   *)
(***************************************************************************)
Inv2 == marked \cup ReachableFrom(vroot) = ReachableFrom(marked \cup vroot)

(***************************************************************************)
(* Auxiliary invariant: what is reachable from acknowledged \cup pending   *)
(* is exactly what is reachable from the root.                            *)
(***************************************************************************)
Inv3 == ReachableFrom(marked \cup vroot) = Reachable

(***************************************************************************)
(* Termination is represented explicitly: "Done" implies nothing pending. *)
(***************************************************************************)
Inv4 == (pc = "Done") => (vroot = {})

Inv == /\ TypeOK
       /\ Inv1
       /\ Inv2
       /\ Inv3
       /\ Inv4

(***************************************************************************)
(* Partial correctness: on termination, marked equals the reachable set.  *)
(* Inv implies PartialCorrectness: at "Done", vroot = {}, so by Inv2 and  *)
(* Inv3, marked = marked \cup ReachableFrom({}) = Reachable.              *)
(***************************************************************************)
PartialCorrectness == (pc = "Done") => (marked = Reachable)

(***************************************************************************)
(* Termination: if the reachable set is finite, the algorithm eventually  *)
(* terminates.                                                             *)
(***************************************************************************)
Termination == IsFinite(Reachable) => <>(pc = "Done")

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Inv => PartialCorrectness
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination
=============================================================================