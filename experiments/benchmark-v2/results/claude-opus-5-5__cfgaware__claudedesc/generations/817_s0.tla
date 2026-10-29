---------------------------- MODULE MCReachable ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root, Succ

(***************************************************************************)
(* Sequences are defined locally (instead of extending Sequences) so that  *)
(* the configuration can override Seq with the bounded LimitedSeq.         *)
(***************************************************************************)
Seq(S) == UNION {[1..n -> S] : n \in Nat}

Len(s) == CHOOSE n \in Nat : DOMAIN s = 1..n

LimitedSeq(S) == UNION {[1..n -> S] : n \in 0..Cardinality(Nodes)}

ConnectedToSomeButNotAll ==
    CHOOSE succ \in [Nodes -> SUBSET Nodes] :
        \A n \in Nodes : Cardinality(succ[n]) = 2

ASSUME SuccAssump == Succ \in [Nodes -> SUBSET Nodes]
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachability definitions                                                *)
(***************************************************************************)
IsPathFromTo(p, m, n) ==
    /\ Len(p) > 0
    /\ p[1] = m
    /\ p[Len(p)] = n
    /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in Succ[p[i]]

ExistsPath(m, n) == \E p \in Seq(Nodes) : IsPathFromTo(p, m, n)

ReachableFrom(S) == {n \in Nodes : \E m \in S : ExistsPath(m, n)}

(***************************************************************************)
(* The algorithm                                                           *)
(***************************************************************************)
VARIABLES marked, vroot, pc

vars == <<marked, vroot, pc>>

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF vroot # {}
          THEN /\ \E v \in vroot :
                    IF v \notin marked
                      THEN /\ marked' = marked \cup {v}
                           /\ vroot' = vroot \cup Succ[v]
                      ELSE /\ vroot' = vroot \ {v}
                           /\ UNCHANGED marked
               /\ pc' = "a"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<marked, vroot>>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom({Root})

Inv3 == (pc = "Done") => (vroot = {})

PartialCorrectness == (pc = "Done") => (marked = ReachableFrom({Root}))

Termination == <>(pc = "Done")
=============================================================================