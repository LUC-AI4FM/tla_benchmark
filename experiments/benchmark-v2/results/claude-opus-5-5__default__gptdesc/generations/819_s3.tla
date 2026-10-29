------------------------------ MODULE ParReach ------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Succ, Root, Procs

ASSUME SuccAssump == Succ \in [Nodes -> SUBSET Nodes]
ASSUME RootAssump == Root \in Nodes
ASSUME ProcsAssump == Procs # {}

ReachableFrom(S) ==
  LET R[n \in Nat] == IF n = 0 THEN S
                      ELSE R[n-1] \cup UNION {Succ[m] : m \in R[n-1]}
  IN  UNION {R[n] : n \in Nat}

Reachable == ReachableFrom({Root})

NoNode == CHOOSE x : x \notin Nodes

(***************************************************************************
--algorithm ParReach {
    variables marked = {}, vroot = {Root};
    fair process (p \in Procs)
      variables u = NoNode, toVroot = {};
    {
    a: while (vroot /= {})
        { with (v \in vroot) { u := v; vroot := vroot \ {v} };
       b: if (u \notin marked)
            { marked := marked \cup {u};
              toVroot := Succ[u];
            c: while (toVroot /= {})
                 { with (w \in toVroot)
                     { vroot := vroot \cup {w};
                       toVroot := toVroot \ {w} }
                 }
            }
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
        /\ u = [self \in Procs |-> NoNode]
        /\ toVroot = [self \in Procs |-> {}]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ IF vroot /= {}
                 THEN /\ \E v \in vroot:
                           /\ u' = [u EXCEPT ![self] = v]
                           /\ vroot' = vroot \ {v}
                      /\ pc' = [pc EXCEPT ![self] = "b"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << vroot, u >>
           /\ UNCHANGED << marked, toVroot >>

b(self) == /\ pc[self] = "b"
           /\ IF u[self] \notin marked
                 THEN /\ marked' = (marked \cup {u[self]})
                      /\ toVroot' = [toVroot EXCEPT ![self] = Succ[u[self]]]
                      /\ pc' = [pc EXCEPT ![self] = "c"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
                      /\ UNCHANGED << marked, toVroot >>
           /\ UNCHANGED << vroot, u >>

c(self) == /\ pc[self] = "c"
           /\ IF toVroot[self] /= {}
                 THEN /\ \E w \in toVroot[self]:
                           /\ vroot' = (vroot \cup {w})
                           /\ toVroot' = [toVroot EXCEPT ![self] = toVroot[self] \ {w}]
                      /\ pc' = [pc EXCEPT ![self] = "c"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
                      /\ UNCHANGED << vroot, toVroot >>
           /\ UNCHANGED << marked, u >>

p(self) == a(self) \/ b(self) \/ c(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to the sequential reachability specification.        *)
(***************************************************************************)
vrootBar == vroot \cup {u[q] : q \in {r \in Procs : pc[r] \in {"b", "c"}}}
                  \cup UNION {toVroot[q] : q \in Procs}

pcBar == IF \A q \in Procs : pc[q] = "Done" THEN "Done" ELSE "a"

RVars == << marked, vrootBar, pcBar >>

(* The imported sequential reachability algorithm, under the mapping. *)
RInit == /\ marked = {}
         /\ vrootBar = {Root}
         /\ pcBar = "a"

Ra == /\ pcBar = "a"
      /\ IF vrootBar /= {}
            THEN /\ \E v \in vrootBar :
                      IF v \notin marked
                        THEN /\ marked' = marked \cup {v}
                             /\ vrootBar' = vrootBar \cup Succ[v]
                        ELSE /\ vrootBar' = vrootBar \ {v}
                             /\ UNCHANGED marked
                 /\ pcBar' = "a"
            ELSE /\ pcBar' = "Done"
                 /\ UNCHANGED << marked, vrootBar >>

RTerminating == pcBar = "Done" /\ UNCHANGED RVars

RNext == Ra \/ RTerminating

RSafetySpec == RInit /\ [][RNext]_RVars

RFairness == WF_RVars(RNext)

RSpec == RSafetySpec /\ RFairness

RCorrectness == pcBar = "Done" => marked = Reachable

RTermination == IsFiniteSet(Reachable) => <>(pcBar = "Done")

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)
TypeOK == /\ marked \subseteq Nodes
          /\ vroot \subseteq Nodes
          /\ u \in [Procs -> Nodes \cup {NoNode}]
          /\ toVroot \in [Procs -> SUBSET Nodes]
          /\ pc \in [Procs -> {"a", "b", "c", "Done"}]

RInv == /\ marked \subseteq Reachable
        /\ vrootBar \subseteq Reachable
        /\ \A m \in marked : Succ[m] \subseteq marked \cup vrootBar
        /\ (pcBar = "Done") => (vrootBar = {})
        /\ Reachable = marked \cup ReachableFrom(vrootBar)

Inv == /\ TypeOK
       /\ \A q \in Procs : pc[q] \in {"b", "c"} => u[q] \in Nodes
       /\ \A q \in Procs : pc[q] = "c" => /\ u[q] \in marked
                                          /\ toVroot[q] \subseteq Succ[u[q]]
       /\ \A q \in Procs : pc[q] # "c" => toVroot[q] = {}
       /\ RInv

Correctness == (\A q \in Procs : pc[q] = "Done") => (marked = Reachable)

TerminatesIffFinite ==
    IsFiniteSet(Reachable) <=> <>(\A q \in Procs : pc[q] = "Done")

-----------------------------------------------------------------------------
THEOREM InvTheorem == Spec => []Inv

THEOREM CorrectnessTheorem == Spec => []Correctness

THEOREM SafetyRefinement == Spec => RSafetySpec

THEOREM FairnessRefinement == Spec => RFairness

THEOREM Refinement == Spec => RSpec

THEOREM TerminationTheorem == Spec => RTermination

THEOREM TerminationIff == Spec => TerminatesIffFinite
=============================================================================