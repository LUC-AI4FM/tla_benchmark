------------------------------ MODULE Reachable ------------------------------
(***************************************************************************)
(* Jayadev Misra's algorithm for computing the set of nodes reachable     *)
(* from a distinguished node Root in a directed graph.  The graph is      *)
(* given by the constants Nodes and Succ of the Reachability module.      *)
(***************************************************************************)
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************
--fair algorithm Reachable {
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
\* BEGIN TRANSLATION
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init == (* Global variables *)
        /\ marked = {}
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

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

(***************************************************************************)
(* Invariants used for proving partial correctness.                       *)
(***************************************************************************)
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == ReachableFrom(marked \cup vroot) = ReachableFrom({Root})

Inv == Inv1 /\ Inv2 /\ Inv3

(***************************************************************************)
(* Partial correctness: upon termination, marked equals the set of nodes  *)
(* reachable from Root.                                                    *)
(***************************************************************************)
PartialCorrectness == (pc = "Done") => (marked = ReachableFrom({Root}))

THEOREM InvariantsHold == Spec => [](TypeOK /\ Inv1 /\ Inv2 /\ Inv3)

THEOREM Correctness == Spec => []PartialCorrectness

(***************************************************************************)
(* Liveness: if the set of nodes reachable from Root is finite, then the  *)
(* algorithm eventually terminates.                                        *)
(***************************************************************************)
THEOREM Liveness ==
  ASSUME IsFiniteSet(ReachableFrom({Root}))
  PROVE  Spec => <>(pc = "Done")
=============================================================================