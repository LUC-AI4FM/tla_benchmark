---------------------------- MODULE ReachableTest ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ

ASSUME /\ Root \in Nodes
       /\ Succ \in [Nodes -> SUBSET Nodes]

(***************************************************************************)
(* Sequences are defined locally so that Seq can be overridden by          *)
(* LimitedSeq for model checking.                                          *)
(***************************************************************************)
Seq(S) == UNION {[1..n -> S] : n \in Nat}

LimitedSeq(S) == UNION {[1..n -> S] : n \in 0..Cardinality(Nodes)}

ConnectedToSomeButNotAll ==
    CHOOSE succ \in [Nodes -> SUBSET Nodes] :
        \A n \in Nodes : Cardinality(succ[n]) = 2

Len(p) == Cardinality(DOMAIN p)

IsPathFromTo(p, m, n) ==
    /\ Len(p) > 0
    /\ p[1] = m
    /\ p[Len(p)] = n
    /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]]

ReachableFrom(S) ==
    {n \in Nodes : \E m \in S : \E p \in Seq(Nodes) : IsPathFromTo(p, m, n)}

VARIABLES marked, vroot, pc

vars == <<marked, vroot, pc>>

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF vroot /= {}
          THEN /\ \E v \in vroot :
                    IF v \notin marked
                      THEN /\ marked' = marked \cup {v}
                           /\ vroot' = (vroot \cup Succ[v]) \ {v}
                      ELSE /\ vroot' = vroot \ {v}
                           /\ UNCHANGED marked
               /\ pc' = "a"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<marked, vroot>>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == ReachableFrom(marked \cup vroot) = ReachableFrom({Root})

PartialCorrectness == (pc = "Done") => (marked = ReachableFrom({Root}))

Termination == <>(pc = "Done")
=============================================================================