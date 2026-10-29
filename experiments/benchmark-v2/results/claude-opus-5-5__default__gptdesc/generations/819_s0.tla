------------------------------ MODULE ParReach ------------------------------
(***************************************************************************)
(* A parallel multiprocess version of Misra's reachability algorithm.      *)
(* A set Procs of processes cooperatively explore the nodes reachable      *)
(* from Root.  They share the variables marked and vroot.  Each process    *)
(* has local variables u and toVroot.  The algorithm terminates iff the    *)
(* set of nodes reachable from Root is finite.  On termination, marked     *)
(* equals ReachableFrom({Root}).                                           *)
(*                                                                         *)
(* The constants Nodes and Succ and the operator ReachableFrom come from   *)
(* module Reachability.  The sequential algorithm is in module Reachable.  *)
(***************************************************************************)
EXTENDS Reachability, Integers, FiniteSets

CONSTANTS Root, Procs

ASSUME RootAssump  == Root \in Nodes
ASSUME ProcsAssump == Procs # {}

(***************************************************************************
--fair algorithm ParallelReachability {
  variables marked = {}, vroot = {Root};
  fair process (p \in Procs)
    variables u = Root, toVroot = {} ;
    {
    a: while (vroot /= {}) {
         with (v \in vroot) { u := v } ;
    b:   if (u \notin marked) {
            marked := marked \cup {u} ;
            toVroot := Succ[u] ;
    c:      while (toVroot /= {}) {
              with (w \in toVroot) {
                vroot := vroot \cup {w} ;
                toVroot := toVroot \ {w} }
            }
          }
         else { vroot := vroot \ {u} }
       }
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES marked, vroot, pc, u, toVroot

vars == << marked, vroot, pc, u, toVroot >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ marked = {}
        /\ vroot = {Root}
        (* Process p *)
        /\ u = [self \in Procs |-> Root]
        /\ toVroot = [self \in Procs |-> {}]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ IF vroot /= {}
                 THEN /\ \E v \in vroot :
                           u' = [u EXCEPT ![self] = v]
                      /\ pc' = [pc EXCEPT ![self] = "b"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ u' = u
           /\ UNCHANGED << marked, vroot, toVroot >>

b(self) == /\ pc[self] = "b"
           /\ IF u[self] \notin marked
                 THEN /\ marked' = (marked \cup {u[self]})
                      /\ toVroot' = [toVroot EXCEPT ![self] = Succ[u[self]]]
                      /\ pc' = [pc EXCEPT ![self] = "c"]
                      /\ vroot' = vroot
                 ELSE /\ vroot' = vroot \ {u[self]}
                      /\ pc' = [pc EXCEPT ![self] = "a"]
                      /\ UNCHANGED << marked, toVroot >>
           /\ u' = u

c(self) == /\ pc[self] = "c"
           /\ IF toVroot[self] /= {}
                 THEN /\ \E w \in toVroot[self] :
                           /\ vroot' = (vroot \cup {w})
                           /\ toVroot' = [toVroot EXCEPT ![self] = toVroot[self] \ {w}]
                      /\ pc' = [pc EXCEPT ![self] = "c"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
                      /\ UNCHANGED << vroot, toVroot >>
           /\ UNCHANGED << marked, u >>

p(self) == a(self) \/ b(self) \/ c(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs : p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* Fairness-based temporal specification asserting weak fairness of every *)
(* process.                                                                *)
(***************************************************************************)
FairSpec == /\ Init /\ [][Next]_vars
            /\ \A self \in Procs : WF_vars(p(self))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to the sequential algorithm of module Reachable.     *)
(***************************************************************************)
vrootBar == vroot \cup UNION {toVroot[q] : q \in Procs}

pcBar == IF \A q \in Procs : pc[q] = "Done" THEN "Done" ELSE "a"

R == INSTANCE Reachable WITH vroot <- vrootBar, pc <- pcBar

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type correctness and an inductive invariant used for the refinement.   *)
(***************************************************************************)
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ u \in [Procs -> Nodes]
          /\ toVroot \in [Procs -> SUBSET Nodes]
          /\ pc \in [Procs -> {"a", "b", "c", "Done"}]

Inv == /\ TypeOK
       /\ \A q \in Procs :
             /\ (pc[q] \in {"a", "b", "Done"}) => (toVroot[q] = {})
             /\ (pc[q] = "b") => (u[q] \in vrootBar \cup marked)
             /\ (pc[q] = "c") => /\ u[q] \in marked
                                 /\ toVroot[q] \subseteq Succ[u[q]]
                                 /\ Succ[u[q]] \subseteq vrootBar
       /\ (\A q \in Procs : pc[q] = "Done") => (vrootBar = {})

PartialCorrectness ==
    (\A q \in Procs : pc[q] = "Done") => (marked = ReachableFrom({Root}))

-----------------------------------------------------------------------------
THEOREM TypeCorrect == Spec => []TypeOK

THEOREM Invariance == Spec => []Inv

THEOREM Refinement == Spec => R!Spec

THEOREM SafetyRefinement == Spec => R!Init /\ [][R!Next]_R!vars

THEOREM FairnessRefinement == Spec => WF_R!vars(R!Next)

THEOREM Correctness == Spec => []PartialCorrectness
=============================================================================