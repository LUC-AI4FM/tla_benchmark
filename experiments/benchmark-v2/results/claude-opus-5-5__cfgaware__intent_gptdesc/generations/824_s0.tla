---------------------------- MODULE Reachable ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Succ, Root

ASSUME SuccAssump == Succ \in [Nodes -> SUBSET Nodes]
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* ReachableFrom(S) is the set of nodes reachable from nodes in S,          *)
(* including S itself, computed as a least fixpoint.                       *)
(***************************************************************************)
ReachableFrom(S) ==
  LET RECURSIVE R(_)
      R(T) == LET U == T \cup UNION {Succ[n] : n \in T}
              IN  IF U = T THEN T ELSE R(U)
  IN  R(S \cap Nodes)

Reachable == ReachableFrom({Root})

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

Spec == Init /\ [][Next]_vars /\ WF_vars(a)

----------------------------------------------------------------------------

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == Reachable = ReachableFrom(marked \cup vroot)

PartialCorrectness == (pc = "Done") => (marked = Reachable)

Termination == <>(pc = "Done")

THEOREM Spec => [](Inv1 /\ Inv2 /\ Inv3)
THEOREM Spec => []PartialCorrectness
THEOREM IsFiniteSet(Reachable) => (Spec => Termination)
=============================================================================