---------------------------- MODULE Reachable ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ

ASSUME RootInNodes == Root \in Nodes
ASSUME SuccType    == Succ \in [Nodes -> SUBSET Nodes]

(***************************************************************************)
(* Sequences are modelled directly as functions with domain 1..n.          *)
(* Seq is unbounded; LimitedSeq caps the length at the number of nodes.    *)
(* A simple path never needs more than that many nodes. The model          *)
(* configuration can substitute LimitedSeq for Seq.                        *)
(***************************************************************************)
Seq(S) == UNION { [1..n -> S] : n \in Nat }

LimitedSeq(S) == UNION { [1..n -> S] : n \in 1..Cardinality(Nodes) }

Len(s) == Cardinality(DOMAIN s)

(***************************************************************************)
(* Reachability with respect to an arbitrary successor function succ.      *)
(***************************************************************************)
IsPathVia(succ, p) ==
    \A i \in 1..(Len(p) - 1) : p[i+1] \in succ[p[i]]

ReachableVia(succ, m, n) ==
    \E p \in Seq(Nodes) :
        /\ Len(p) > 0
        /\ p[1] = m
        /\ p[Len(p)] = n
        /\ IsPathVia(succ, p)

ReachableFromVia(succ, S) ==
    { n \in Nodes : \E m \in S : ReachableVia(succ, m, n) }

(***************************************************************************)
(* Reachability with respect to the constant Succ.                         *)
(***************************************************************************)
Reachable(m, n) == ReachableVia(Succ, m, n)

ReachableFrom(S) == ReachableFromVia(Succ, S)

MutuallyReachable(m, n) == Reachable(m, n) /\ Reachable(n, m)

MutuallyReachableSet == { n \in Nodes : \A m \in Nodes : MutuallyReachable(m, n) }

(***************************************************************************)
(* Predicates over candidate successor relations.                          *)
(***************************************************************************)
TwoSuccessors(succ) ==
    \A n \in Nodes : Cardinality(succ[n]) = 2

ReachableFromEveryOther(succ) ==
    \E n \in Nodes : \A m \in Nodes \ {n} : ReachableVia(succ, m, n)

ReachableFromSomeButNotAll(succ) ==
    \E n \in Nodes :
        /\ \E m \in Nodes \ {n} : ReachableVia(succ, m, n)
        /\ \E m \in Nodes \ {n} : ~ReachableVia(succ, m, n)

(***************************************************************************)
(* Nondeterministically chosen successor relations.                        *)
(***************************************************************************)
TwoSuccessorRelations ==
    { succ \in [Nodes -> SUBSET Nodes] : TwoSuccessors(succ) }

ConnectedToSomeButNotAll ==
    CHOOSE succ \in [Nodes -> SUBSET Nodes] : ReachableFromSomeButNotAll(succ)

(***************************************************************************)
(* Marking algorithm that computes the set of nodes reachable from Root.   *)
(***************************************************************************)
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

a ==
    /\ pc = "a"
    /\ IF vroot # {}
          THEN /\ \E v \in vroot :
                    IF v \notin marked
                       THEN /\ marked' = marked \cup {v}
                            /\ vroot' = vroot \cup Succ[v]
                       ELSE /\ vroot' = vroot \ {v}
                            /\ UNCHANGED marked
               /\ pc' = "a"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(a)

(***************************************************************************)
(* Invariants and correctness properties.                                  *)
(***************************************************************************)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

Inv1 ==
    /\ TypeOK
    /\ \A n \in marked \ vroot : Succ[n] \subseteq (marked \cup vroot)

Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom({Root})

Inv3 ==
    /\ marked \subseteq ReachableFrom({Root})
    /\ vroot \subseteq ReachableFrom({Root})

PartialCorrectness ==
    (pc = "Done") => (marked = ReachableFrom({Root}))

Termination == <>(pc = "Done")

=============================================================================