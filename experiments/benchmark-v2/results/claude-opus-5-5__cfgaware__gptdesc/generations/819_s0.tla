------------------------------ MODULE ParReach ------------------------------
EXTENDS Reachability, Integers, FiniteSets

CONSTANTS Root, Procs

ASSUME RootAssump == Root \in Nodes
ASSUME ProcsAssump == Procs # {} /\ IsFiniteSet(Procs)

(***************************************************************************
--fair algorithm ParallelReach {
   variables marked = {}, vroot = {Root};
   fair process (p \in Procs)
     variables u = Root, toVroot = {} ;
   { a: while (vroot /= {})
          { with (v \in vroot) { u := v ;
                                 vroot := vroot \ {v} } ;
         b: if (u \notin marked)
              { marked := marked \cup {u} ;
                toVroot := Succ[u] ;
             c: while (toVroot /= {})
                  { with (w \in toVroot) {
                      vroot := vroot \cup {w} ;
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
        /\ u = [self \in Procs |-> Root]
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
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ u \in [Procs -> Nodes]
          /\ toVroot \in [Procs -> SUBSET Nodes]
          /\ pc \in [Procs -> {"a", "b", "c", "Done"}]

Inv == /\ TypeOK
       /\ \A q \in Procs :
             /\ pc[q] \in {"a", "b", "Done"} => (toVroot[q] = {})
             /\ (pc[q] = "c") => (u[q] \in marked)

vrootBar == vroot \cup {u[i] : i \in {q \in Procs : pc[q] = "b"}}
                  \cup UNION {toVroot[i] : i \in Procs}

pcBar == IF \A q \in Procs : pc[q] = "Done" THEN "Done" ELSE "a"

R == INSTANCE Reachable WITH vroot <- vrootBar, pc <- pcBar

THEOREM Spec => []Inv

THEOREM Spec => R!Init /\ [][R!Next]_(R!vars)

THEOREM Spec => R!Spec
=============================================================================