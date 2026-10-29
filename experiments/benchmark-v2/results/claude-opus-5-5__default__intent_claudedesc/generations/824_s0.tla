------------------------------ MODULE Reachable ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Succ, Root

ASSUME SuccAssump == Succ \in [Nodes -> SUBSET Nodes]
ASSUME RootAssump == Root \in Nodes

RECURSIVE ReachableFromSet(_)
ReachableFromSet(S) ==
    LET T == S \cup UNION {Succ[n] : n \in S}
    IN  IF T = S THEN S ELSE ReachableFromSet(T)

ReachableFrom(S) ==
    LET R[i \in Nat] == IF i = 0 THEN S
                        ELSE R[i-1] \cup UNION {Succ[n] : n \in R[i-1]}
    IN  UNION {R[i] : i \in Nat}

Reachable == ReachableFromSet({Root})

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

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

PartialCorrectness == (pc = "Done") => (marked = Reachable)

Inv == /\ TypeOK
       /\ marked \subseteq Reachable
       /\ vroot \subseteq Reachable
       /\ Root \in marked \cup vroot
       /\ \A n \in marked : Succ[n] \subseteq marked \cup vroot
       /\ (pc = "Done") => (marked = Reachable)

Termination == IsFiniteSet(Reachable) => <>(pc = "Done")

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination
==============================================================================