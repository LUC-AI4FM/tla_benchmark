---------------------------- MODULE Reachable ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq(_)

ASSUME RootAssump == Root \in Nodes
ASSUME SuccAssump == Succ \in [Nodes -> SUBSET Nodes]

Len(p) == Cardinality(DOMAIN p)

IsPathFromTo(p, m, n) ==
  /\ Len(p) > 0
  /\ DOMAIN p = 1..Len(p)
  /\ p[1] = m
  /\ p[Len(p)] = n
  /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]]

ExistsPath(m, n) == \E p \in Seq(Nodes) : IsPathFromTo(p, m, n)

ReachableFrom(S) == {n \in Nodes : \E m \in S : ExistsPath(m, n)}

ConnectedToSomeButNotAll ==
  CHOOSE succ \in [Nodes -> SUBSET Nodes] :
    \A n \in Nodes : Cardinality(succ[n]) = 2

LimitedSeq(S) == UNION {[1..k -> S] : k \in 1..Cardinality(Nodes)}

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

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom({Root})

Inv3 == marked \subseteq ReachableFrom({Root})

PartialCorrectness == (pc = "Done") => (marked = ReachableFrom({Root}))

=============================================================================