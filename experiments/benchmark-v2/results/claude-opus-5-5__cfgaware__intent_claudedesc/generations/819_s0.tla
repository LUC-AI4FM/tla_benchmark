------------------------------ MODULE ParReach ------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Root, Procs

ASSUME ProcsAssump == /\ Procs # {}
                      /\ IsFiniteSet(Procs)

(***************************************************************************)
(* The directed graph: a set of nodes and a successor function.            *)
(***************************************************************************)
Nodes == {Root} \cup (1..4)

Succ == [n \in Nodes |->
           IF n = Root THEN {1, 2}
           ELSE IF n = 1 THEN {2}
           ELSE IF n = 2 THEN {3}
           ELSE IF n = 3 THEN {2}
           ELSE {1}]

(***************************************************************************)
(* The set of nodes reachable from Root, computed as a least fixpoint.     *)
(***************************************************************************)
RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  LET T == S \cup UNION {Succ[n] : n \in S}
  IN  IF T = S THEN S ELSE ReachFrom(T)

Reachable == ReachFrom({Root})

(***************************************************************************
--algorithm ParReach {
    variables marked = {}, vroot = {Root};
    fair process (p \in Procs)
      variables u = Root, toVroot = {};
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

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs : p(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
TypeOK == /\ marked \subseteq Nodes
          /\ vroot \subseteq Nodes
          /\ u \in [Procs -> Nodes]
          /\ toVroot \in [Procs -> SUBSET Nodes]
          /\ pc \in [Procs -> {"a", "b", "c", "Done"}]

Inv == /\ TypeOK
       /\ marked \subseteq Reachable
       /\ vroot \subseteq Reachable
       /\ Root \in marked \cup vroot
       /\ \A q \in Procs :
            /\ (pc[q] = "b") => u[q] \in Reachable
            /\ (pc[q] = "c") => /\ u[q] \in marked
                                /\ toVroot[q] \subseteq Succ[u[q]]
            /\ (pc[q] \in {"a", "b", "Done"}) => toVroot[q] = {}
       /\ \A n \in marked :
            Succ[n] \subseteq marked \cup vroot \cup UNION {toVroot[q] : q \in Procs}

Safety == marked \subseteq Reachable

PartialCorrectness ==
  (\A self \in ProcSet : pc[self] = "Done") => (marked = Reachable)

=============================================================================