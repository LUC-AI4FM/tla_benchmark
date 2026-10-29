------------------------------ MODULE Reachable ------------------------------
(***************************************************************************)
(* Jayadev Misra's algorithm for computing the set of nodes reachable     *)
(* from a root node in a directed graph.  It is a variant of breadth-     *)
(* first search designed to facilitate parallel implementation.           *)
(*                                                                         *)
(* The module Reachability defines the constants Nodes and Succ, where    *)
(* Succ \in [Nodes -> SUBSET Nodes], and the operator ReachableFrom.      *)
(***************************************************************************)
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

Reachable == ReachableFrom({Root})

(***************************************************************************
--algorithm Reachable {
    variables marked = {}, vroot = {Root};
    { a: while (vroot /= {})
           { with (v \in vroot)
               { if (v \notin marked)
                   { marked := marked \cup {v};
                     vroot  := vroot \cup Succ[v] }
                 else { vroot := vroot \ {v} }
               }
           }
    }
}
 ***************************************************************************)

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF vroot /= {}
          THEN /\ \E v \in vroot :
                    IF v \notin marked
                      THEN /\ marked' = (marked \cup {v})
                           /\ vroot' = (vroot \cup Succ[v])
                      ELSE /\ vroot' = vroot \ {v}
                           /\ UNCHANGED marked
               /\ pc' = "a"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == Reachable = ReachableFrom(marked \cup vroot)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)
PartialCorrectness == [](pc = "Done" => (marked = Reachable))

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3

THEOREM Spec => PartialCorrectness

THEOREM IsFiniteSet(Reachable) => (Spec => <>(pc = "Done"))
=============================================================================