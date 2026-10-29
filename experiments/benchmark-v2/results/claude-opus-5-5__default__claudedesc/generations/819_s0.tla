------------------------------ MODULE ParReach ------------------------------
EXTENDS Reachability, Integers, FiniteSets

CONSTANTS Root, Procs

ASSUME RootAssump == Root \in Nodes

ASSUME ProcsAssump == /\ Procs # {}
                      /\ IsFiniteSet(Procs)

(***************************************************************************
--algorithm ParallelReach {
  variables marked = {}, vroot = {Root};
  fair process (p \in Procs)
     variables u = Root, toVroot = {} ;
    { a: while (vroot /= {})
          { with (v \in vroot) { u := v } ;
            b: if (u \notin marked)
                 { marked := marked \cup {u};
                   toVroot := Succ[u] ;
                   c: while (toVroot /= {})
                        { with (w \in toVroot) {
                            vroot := vroot \cup {w} ;
                            toVroot := toVroot \ {w} }
                        }
                 }
               else { vroot := vroot \ {u} }
          }
    }
}
***************************************************************************)

VARIABLES marked, vroot, pc, u, toVroot

vars == << marked, vroot, pc, u, toVroot >>

ProcSet == Procs

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ u = [self \in Procs |-> Root]
        /\ toVroot = [self \in Procs |-> {}]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ IF vroot /= {}
                 THEN /\ \E v \in vroot : u' = [u EXCEPT ![self] = v]
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

-----------------------------------------------------------------------------
(***************************************************************************)
(* Inductive invariant: type correctness plus control-state relationships. *)
(***************************************************************************)
Inv == /\ marked \in SUBSET Nodes
       /\ vroot \in SUBSET Nodes
       /\ u \in [Procs -> Nodes]
       /\ toVroot \in [Procs -> SUBSET Nodes]
       /\ pc \in [Procs -> {"a", "b", "c", "Done"}]
       /\ \A q \in Procs :
             /\ (pc[q] \in {"a", "b", "Done"}) => (toVroot[q] = {})
             /\ (pc[q] = "b") => (u[q] \in vroot \cup marked)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to Misra's sequential algorithm (module Reachable).  *)
(***************************************************************************)
vrootBar == vroot \cup UNION {toVroot[i] : i \in Procs}

pcBar == IF \A q \in Procs : pc[q] = "Done" THEN "Done" ELSE "a"

R == INSTANCE Reachable WITH vroot <- vrootBar, pc <- pcBar

THEOREM InvTheorem == Spec => []Inv

THEOREM SafetyRefinement ==
  Spec => /\ R!Init
          /\ [][R!Next]_<< marked, vrootBar, pcBar >>

THEOREM LivenessRefinement ==
  Spec => WF_<< marked, vrootBar, pcBar >>(R!Next)

THEOREM Refinement == Spec => R!Spec
=============================================================================