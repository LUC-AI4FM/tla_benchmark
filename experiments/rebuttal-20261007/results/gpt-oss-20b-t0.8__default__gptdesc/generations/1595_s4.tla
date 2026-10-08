------------------------------ MODULE Counter ------------------------------
EXTENDS Naturals, TLC

VARIABLES x, pc

(* Initial condition *)
Init == /\ x = 0
        /\ pc = "Loop"

(* Next-state relation *)
Next ==
  \/ /\ pc = "Loop"
     /\ x < 10
     /\ x' = x + 1
     /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ x >= 10
     /\ x' = x
     /\ pc' = "Done"
  \/ /\ pc = "Done"
     /\ pc' = "Done"
     /\ x' = x

(* Safety invariant *)
Safe == /\ x \in 0..10
        /\ pc \in {"Loop", "Done"}

(* Auxiliary predicates *)
AtFive      == (x = 5)
FinishLoop  == (x >= 10)

(* Liveness properties *)
Termination   == <> (pc = "Done")
PossibleCounts == \A n \in 0..10 : <> (x = n)

(* Specification with weak fairness on Next *)
Spec == Init
       /\ [][Next]_<<x, pc>>
       /\ WF_vars(Next)
       /\ Safe
       /\ Termination
       /\ PossibleCounts

=============================================================================