---------------------------- MODULE MCReachable ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, n3, n4

Nodes == {n1, n2, n3, n4}

root == n1

ConnectedToSomeButNotAll ==
  CHOOSE succ \in [Nodes -> SUBSET Nodes] :
     \A n \in Nodes : Cardinality(succ[n]) = 2

Succ == ConnectedToSomeButNotAll

LimitedSeq(S) == UNION { [1..k -> S] : k \in 0..Cardinality(Nodes) }

IsPathFromTo(p, m, n) ==
  /\ Len(p) > 0
  /\ p[1] = m
  /\ p[Len(p)] = n
  /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in Succ[p[i]]

ReachableFrom(S) ==
  { n \in Nodes : \E m \in S : \E p \in LimitedSeq(Nodes) : IsPathFromTo(p, m, n) }

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init ==
  /\ marked = {}
  /\ vroot = {root}
  /\ pc = "a"

a ==
  /\ pc = "a"
  /\ IF vroot /= {}
       THEN \E v \in vroot :
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

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ vroot \in SUBSET Nodes
  /\ pc \in {"a", "Done"}
  /\ (pc = "Done") => (vroot = {})

Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom({root})

Inv3 == (marked \cup vroot) \subseteq ReachableFrom({root})

PartialCorrectness == (pc = "Done") => (marked = ReachableFrom({root}))

Termination == <>(pc = "Done")

THEOREM Spec => [](TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness)
THEOREM Spec => Termination
=============================================================================