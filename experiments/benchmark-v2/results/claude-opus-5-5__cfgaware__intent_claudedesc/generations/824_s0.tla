------------------------------- MODULE Reachable -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Succ, Root

ASSUME SuccAssump == Succ \in [Nodes -> SUBSET Nodes]
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* ReachableFrom(S) is the set of nodes reachable from nodes in S,        *)
(* including S itself, by following zero or more Succ edges.              *)
(***************************************************************************)
ReachableFrom(S) ==
  LET RF[n \in Nat] ==
        IF n = 0 THEN S
                 ELSE RF[n-1] \cup UNION {Succ[x] : x \in RF[n-1]}
  IN  RF[Cardinality(Nodes)]

Reachable == ReachableFrom({Root})

(***************************************************************************
--algorithm Reachable {
  variables marked = {}, vroot = {Root};
  { a: while (vroot # {})
         { with (v \in vroot)
             { if (v \notin marked)
                 { marked := marked \cup {v};
                   vroot  := vroot \cup Succ[v] }
               else { vroot := vroot \ {v} }
             }
         }
  }
}
***************************************************************************)
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF vroot # {}
          THEN /\ \E v \in vroot :
                    IF v \notin marked
                      THEN /\ marked' = (marked \cup {v})
                           /\ vroot' = (vroot \cup Succ[v])
                      ELSE /\ vroot' = vroot \ {v}
                           /\ UNCHANGED marked
               /\ pc' = "a"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = Reachable

Inv3 == /\ marked \subseteq Reachable
        /\ vroot \subseteq Reachable

PartialCorrectness == (pc = "Done") => (marked = Reachable)

=============================================================================