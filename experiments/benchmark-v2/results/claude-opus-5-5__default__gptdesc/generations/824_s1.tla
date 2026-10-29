----------------------------- MODULE Reachable -----------------------------
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
(* Invariants used for proving partial correctness.                        *)
(***************************************************************************)
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == ReachableFrom({Root}) = ReachableFrom(marked \cup vroot)

(***************************************************************************)
(* Partial correctness: upon termination, marked is the reachable set.     *)
(***************************************************************************)
THEOREM PartialCorrectness ==
  Spec => [](pc = "Done" => marked = ReachableFrom({Root}))

(***************************************************************************)
(* Liveness: the algorithm terminates if the reachable set is finite.      *)
(***************************************************************************)
THEOREM TerminationThm ==
  ASSUME IsFiniteSet(ReachableFrom({Root}))
  PROVE  Spec => <>(pc = "Done")
=============================================================================