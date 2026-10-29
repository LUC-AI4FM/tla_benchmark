---------------------------- MODULE ParReach ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Succ, Root, Procs

ASSUME /\ Succ \in [Nodes -> SUBSET Nodes]
       /\ Root \in Nodes
       /\ IsFiniteSet(Procs)
       /\ Procs # {}

VARIABLES marked, vroot, pc, u, toVroot

vars == <<marked, vroot, pc, u, toVroot>>

ProcSet == Procs

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ u = [self \in Procs |-> Root]
        /\ toVroot = [self \in Procs |-> {}]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ IF vroot # {}
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
           /\ IF toVroot[self] # {}
                 THEN /\ \E w \in toVroot[self] :
                           /\ vroot' = (vroot \cup {w})
                           /\ toVroot' = [toVroot EXCEPT ![self] = toVroot[self] \ {w}]
                      /\ pc' = [pc EXCEPT ![self] = "c"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
                      /\ UNCHANGED << vroot, toVroot >>
           /\ UNCHANGED << marked, u >>

p(self) == a(self) \/ b(self) \/ c(self)

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs : p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

-----------------------------------------------------------------------------

Inv == /\ marked \in SUBSET Nodes
       /\ vroot \in SUBSET Nodes
       /\ u \in [Procs -> Nodes]
       /\ toVroot \in [Procs -> SUBSET Nodes]
       /\ pc \in [Procs -> {"a", "b", "c", "Done"}]
       /\ \A q \in Procs :
             /\ (pc[q] \in {"a", "b", "Done"}) => (toVroot[q] = {})
             /\ (pc[q] = "b") => (u[q] \in vroot \cup marked)
             /\ (pc[q] = "c") => (u[q] \in marked)

-----------------------------------------------------------------------------
(* Refinement mapping to Misra's sequential algorithm *)

vrootBar == vroot \cup UNION {toVroot[i] : i \in Procs}

pcBar == IF \A q \in Procs : pc[q] = "Done" THEN "Done" ELSE "a"

mvars == << marked, vrootBar, pcBar >>

MInit == /\ marked = {}
         /\ vrootBar = {Root}
         /\ pcBar = "a"

Ma == /\ pcBar = "a"
      /\ IF vrootBar # {}
            THEN /\ \E v \in vrootBar :
                      IF v \notin marked
                         THEN /\ marked' = (marked \cup {v})
                              /\ vrootBar' = (vrootBar \cup Succ[v])
                         ELSE /\ vrootBar' = vrootBar \ {v}
                              /\ marked' = marked
                 /\ pcBar' = "a"
            ELSE /\ pcBar' = "Done"
                 /\ UNCHANGED << marked, vrootBar >>

MTerminating == pcBar = "Done" /\ UNCHANGED mvars

MNext == Ma \/ MTerminating

MSpec == MInit /\ [][MNext]_mvars /\ WF_mvars(MNext)

MSafeSpec == MInit /\ [][MNext]_mvars

MLiveSpec == WF_mvars(MNext)

THEOREM Spec => []Inv

THEOREM SafetyRefinement == Spec => MSafeSpec

THEOREM LivenessRefinement == Spec => MLiveSpec

THEOREM Refinement == Spec => MSpec
=============================================================================