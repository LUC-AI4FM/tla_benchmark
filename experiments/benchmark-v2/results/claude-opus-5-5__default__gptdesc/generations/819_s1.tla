------------------------------ MODULE ParReach ------------------------------
(***************************************************************************)
(* A parallel multiprocess version of Misra's reachability algorithm.      *)
(* A set Procs of processes cooperatively explore the nodes reachable from *)
(* Root, sharing the variables marked and vroot.  Each process has local   *)
(* variables u and toVroot.  The algorithm terminates iff the set of nodes *)
(* reachable from Root is finite, and when it terminates marked equals     *)
(* that set.  We show that it refines the abstract algorithm Reachable.    *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

---------------------------- MODULE Reachable ------------------------------
(***************************************************************************)
(* The abstract (sequential) reachability specification that is imported  *)
(* and refined by the parallel algorithm.                                  *)
(***************************************************************************)
CONSTANTS Nodes, Succ, Root

ASSUME RAssump == /\ Succ \in [Nodes -> SUBSET Nodes]
                  /\ Root \in Nodes

ReachableFrom(S) ==
  LET Closed(T) == /\ S \subseteq T
                   /\ \A n \in T : Succ[n] \subseteq T
  IN  {n \in Nodes : \A T \in SUBSET Nodes : Closed(T) => n \in T}

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

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

SafeSpec == Init /\ [][Next]_vars

Fairness == WF_vars(Next)

Spec == SafeSpec /\ Fairness

Termination == <>(pc = "Done")

PartialCorrectness == (pc = "Done") => (marked = ReachableFrom({Root}))

THEOREM Spec => []PartialCorrectness
THEOREM Spec => (IsFiniteSet(ReachableFrom({Root})) => Termination)
=============================================================================