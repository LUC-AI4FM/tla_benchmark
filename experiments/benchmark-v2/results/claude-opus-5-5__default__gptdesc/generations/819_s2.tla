------------------------------ MODULE ParReach ------------------------------
(***************************************************************************)
(* A parallel multiprocess version of Misra's reachability algorithm.      *)
(* The sequential reachability specification is given as an inner module   *)
(* (Reachable), which the parallel algorithm is shown to refine.           *)
(***************************************************************************)

  ---------------------------- MODULE Reachable ----------------------------
  EXTENDS Integers, Sequences, FiniteSets

  CONSTANTS Nodes, Succ, Root

  ASSUME SuccAssump == Succ \in [Nodes -> SUBSET Nodes]
  ASSUME RootAssump == Root \in Nodes

  IsPathFromTo(p, m, n) ==
      /\ Len(p) > 0
      /\ p[1] = m
      /\ p[Len(p)] = n
      /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]]

  ReachableFrom(S) ==
      {n \in Nodes : \E m \in S : \E p \in Seq(Nodes) : IsPathFromTo(p, m, n)}

  VARIABLES marked, vroot, pc

  vars == << marked, vroot, pc >>

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
                 /\ UNCHANGED << marked, vroot >>

  Terminating == pc = "Done" /\ UNCHANGED vars

  Next == a \/ Terminating

  SafeSpec == Init /\ [][Next]_vars

  Fairness == WF_vars(Next)

  Spec == SafeSpec /\ Fairness

  PartialCorrectness == (pc = "Done") => (marked = ReachableFrom({Root}))

  Termination == <>(pc = "Done")
  ==========================================================================