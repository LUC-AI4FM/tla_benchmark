---------------------------- MODULE MCParReach ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, Procs, Succ

ASSUME Root \in Nodes
ASSUME Succ \in [Nodes -> SUBSET Nodes]

-----------------------------------------------------------------------------
(* Graph used for model checking: every node has exactly two successors.   *)
ConnectedToSomeButNotAll ==
    CHOOSE succ \in [Nodes -> SUBSET Nodes] :
        \A n \in Nodes : Cardinality(succ[n]) = 2

(* Bounded version of Seq, used to override Seq so the state space is finite. *)
LimitedSeq(S) == UNION { [1..n -> S] : n \in 0..Cardinality(Nodes) }

(* The set of nodes reachable from Root, defined by paths in the graph.      *)
Reachable ==
    { n \in Nodes :
        \E p \in Seq(Nodes) :
            /\ Len(p) > 0
            /\ p[1] = Root
            /\ p[Len(p)] = n
            /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in Succ[p[i]] }

-----------------------------------------------------------------------------
(* The ParReach algorithm                                                    *)
VARIABLES marked, vroot, pc, u, toVroot

vars == <<marked, vroot, pc, u, toVroot>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ vroot \subseteq Nodes
    /\ pc \in [Procs -> {"a", "b", "c", "Done"}]
    /\ u \in [Procs -> Nodes]
    /\ toVroot \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = [p \in Procs |-> "a"]
    /\ u = [p \in Procs |-> Root]
    /\ toVroot = [p \in Procs |-> {}]

a(self) ==
    /\ pc[self] = "a"
    /\ IF vroot /= {}
         THEN /\ \E v \in vroot :
                    /\ u' = [u EXCEPT ![self] = v]
                    /\ vroot' = vroot \ {v}
              /\ pc' = [pc EXCEPT ![self] = "b"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED <<u, vroot>>
    /\ UNCHANGED <<marked, toVroot>>

b(self) ==
    /\ pc[self] = "b"
    /\ IF u[self] \notin marked
         THEN /\ marked' = marked \cup {u[self]}
              /\ toVroot' = [toVroot EXCEPT ![self] = Succ[u[self]]]
              /\ pc' = [pc EXCEPT ![self] = "c"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
              /\ UNCHANGED <<marked, toVroot>>
    /\ UNCHANGED <<vroot, u>>

c(self) ==
    /\ pc[self] = "c"
    /\ IF toVroot[self] /= {}
         THEN /\ \E w \in toVroot[self] :
                    /\ vroot' = vroot \cup {w}
                    /\ toVroot' = [toVroot EXCEPT ![self] = toVroot[self] \ {w}]
              /\ pc' = pc
         ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
              /\ UNCHANGED <<vroot, toVroot>>
    /\ UNCHANGED <<marked, u>>

proc(self) == a(self) \/ b(self) \/ c(self)

Terminating ==
    /\ \A self \in Procs : pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in Procs : proc(self)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A self \in Procs : WF_vars(proc(self))

-----------------------------------------------------------------------------
(* Refinement mapping to the sequential reachability algorithm              *)
vrootBar ==
    vroot
      \cup { u[i] : i \in { q \in Procs : pc[q] \in {"b", "c"} } }
      \cup UNION { toVroot[i] : i \in Procs }

pcBar == IF \A q \in Procs : pc[q] = "Done" THEN "Done" ELSE "a"

RVars == <<marked, vrootBar, pcBar>>

RInit ==
    /\ marked = {}
    /\ vrootBar = {Root}
    /\ pcBar = "a"

RA ==
    /\ pcBar = "a"
    /\ IF vrootBar /= {}
         THEN /\ \E v \in vrootBar :
                    IF v \notin marked
                      THEN /\ marked' = marked \cup {v}
                           /\ vrootBar' = vrootBar \cup Succ[v]
                      ELSE /\ vrootBar' = vrootBar \ {v}
                           /\ marked' = marked
              /\ pcBar' = "a"
         ELSE /\ pcBar' = "Done"
              /\ marked' = marked
              /\ vrootBar' = vrootBar

RTerminating == pcBar = "Done" /\ UNCHANGED RVars

RNext == RA \/ RTerminating

Refines == RInit /\ [][RNext]_RVars /\ WF_RVars(RNext)

-----------------------------------------------------------------------------
(* Safety invariant                                                          *)
Inv ==
    /\ TypeOK
    /\ marked \subseteq Reachable
    /\ vrootBar \subseteq Reachable
    /\ Root \in marked \cup vrootBar
    /\ \A m \in marked :
         \/ Succ[m] \subseteq marked \cup vrootBar
         \/ \E q \in Procs : pc[q] = "b" /\ u[q] = m
    /\ (\A q \in Procs : pc[q] = "Done") => (marked = Reachable)

=============================================================================