------------------------------ MODULE ParReach ------------------------------
(***************************************************************************)
(* A parallel multiprocess version of Misra's reachability algorithm.     *)
(* A set Procs of processes cooperatively explore the nodes reachable     *)
(* from the node Root.  They share the sets `marked' and `vroot'; each    *)
(* process has local variables `u' and `toVroot'.  The algorithm          *)
(* terminates iff the set of nodes reachable from Root is finite, and on  *)
(* termination `marked' equals that set.                                  *)
(*                                                                         *)
(* The abstract (sequential) reachability specification is included in   *)
(* this module, expressed directly in terms of the refinement mapping, so *)
(* that the module is self-contained.                                     *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Succ, Root, Procs

ASSUME SuccAssump == Succ \in [Nodes -> SUBSET Nodes]
ASSUME RootAssump == Root \in Nodes
ASSUME ProcsAssump == Procs # {}

(***************************************************************************)
(* The set of nodes reachable from a set S of nodes.                      *)
(***************************************************************************)
ReachableFrom(S) ==
  LET R[n \in Nat] == IF n = 0 THEN S
                                ELSE R[n-1] \cup UNION {Succ[x] : x \in R[n-1]}
  IN  UNION {R[n] : n \in Nat}

Reachable == ReachableFrom({Root})

NoNode == CHOOSE x : x \notin Nodes

(***************************************************************************
--algorithm ParallelReachability {
  variables marked = {}, vroot = {Root};
  fair process (p \in Procs)
    variables u = NoNode, toVroot = {} ;
  { a: while (vroot /= {})
        { with (v \in vroot) { u := v };
       b: if (u \notin marked)
            { marked := marked \cup {u};
              toVroot := Succ[u];
           c: while (toVroot /= {})
                { with (w \in toVroot)
                    { vroot := vroot \cup {w};
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

ProcSet == Procs

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ u = [self \in Procs |-> NoNode]
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
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")
\* END TRANSLATION

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
TypeOK == /\ marked \subseteq Nodes
          /\ vroot \subseteq Nodes
          /\ u \in [Procs -> Nodes \cup {NoNode}]
          /\ toVroot \in [Procs -> SUBSET Nodes]
          /\ pc \in [Procs -> {"a", "b", "c", "Done"}]

(***************************************************************************)
(* The refinement mapping.                                                 *)
(***************************************************************************)
vrootBar == vroot \cup UNION {toVroot[i] : i \in Procs}

pcBar == IF \A q \in Procs : pc[q] = "Done" THEN "Done" ELSE "a"

absVars == << marked, vrootBar, pcBar >>

(***************************************************************************)
(* The (sequential) reachability specification, i.e. the translation of  *)
(*                                                                         *)
(*   variables marked = {}, vroot = {Root};                                *)
(*   { a: while (vroot /= {})                                              *)
(*          { with (v \in vroot)                                           *)
(*              { if (v \notin marked)                                     *)
(*                  { marked := marked \cup {v};                           *)
(*                    vroot := vroot \cup Succ[v] }                        *)
(*                else { vroot := vroot \ {v} } } } }                      *)
(*                                                                         *)
(* with vroot replaced by vrootBar and pc replaced by pcBar.              *)
(***************************************************************************)
RInit == /\ marked = {}
         /\ vrootBar = {Root}
         /\ pcBar = "a"

Ra == /\ pcBar = "a"
      /\ IF vrootBar /= {}
            THEN /\ \E v \in vrootBar :
                      IF v \notin marked
                         THEN /\ marked' = (marked \cup {v})
                              /\ vrootBar' = (vrootBar \cup Succ[v])
                         ELSE /\ vrootBar' = vrootBar \ {v}
                              /\ marked' = marked
                 /\ pcBar' = "a"
            ELSE /\ pcBar' = "Done"
                 /\ UNCHANGED << marked, vrootBar >>

RTerminating == /\ pcBar = "Done"
                /\ UNCHANGED absVars

RNext == Ra \/ RTerminating

RSafeSpec == RInit /\ [][RNext]_absVars

RFairness == WF_absVars(RNext)

RSpec == RSafeSpec /\ RFairness

RPartialCorrectness == (pcBar = "Done") => (marked = Reachable)

RTermination == IsFiniteSet(Reachable) => <>(pcBar = "Done")

(***************************************************************************)
(* The inductive invariant used to prove the refinement.                  *)
(***************************************************************************)
Inv == /\ TypeOK
       /\ \A q \in Procs :
            /\ (pc[q] \in {"a", "Done"}) => (toVroot[q] = {})
            /\ (pc[q] = "b") => /\ u[q] \in vroot \cup marked
                                /\ toVroot[q] = {}
            /\ (pc[q] = "c") => /\ u[q] \in marked
                                /\ toVroot[q] \subseteq Succ[u[q]]
       /\ marked \subseteq Reachable
       /\ vrootBar \subseteq Reachable
       /\ Root \in marked \cup vrootBar
       /\ \A n \in marked : Succ[n] \subseteq marked \cup vrootBar
       /\ (pcBar = "Done") => (vrootBar = {})

(***************************************************************************)
(* Correctness properties of the parallel algorithm.                       *)
(***************************************************************************)
PartialCorrectness ==
  (\A q \in Procs : pc[q] = "Done") => (marked = Reachable)

ParTermination ==
  IsFiniteSet(Reachable) => <>(\A q \in Procs : pc[q] = "Done")

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM Invariance == Spec => []Inv

THEOREM SafetyRefinement == Spec => RSafeSpec

THEOREM FairnessRefinement == Spec => RFairness

THEOREM Refinement == Spec => RSpec

THEOREM Correctness == Spec => []PartialCorrectness

THEOREM Terminates == Spec => ParTermination
=============================================================================