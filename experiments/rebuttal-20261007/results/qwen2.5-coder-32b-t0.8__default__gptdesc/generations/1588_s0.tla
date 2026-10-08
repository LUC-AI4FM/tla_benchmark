------------------------------ MODULE EuclidAlgorithm ------------------------------
EXTENDS Integers, TLC

CONSTANTS N

VARIABLES pc, u, v, v_ini

Init == /\ pc = "Start"
        /\ u = 24
        /\ v \in 1..N
        /\ v_ini = v

Next ==
    \/ /\ pc = "Start"
       /\ u >= v
       /\ u' = u - v
       /\ v' = v
       /\ v_ini' = v_ini
       /\ pc' = "Subtract"
    \/ /\ pc = "Start"
       /\ u < v
       /\ u' = u
       /\ v' = v - u
       /\ v_ini' = v_ini
       /\ pc' = "Subtract"
    \/ /\ pc = "Subtract"
       /\ u >= v
       /\ u' = u - v
       /\ v' = v
       /\ v_ini' = v_ini
       /\ pc' = "Check"
    \/ /\ pc = "Subtract"
       /\ u < v
       /\ u' = u
       /\ v' = v - u
       /\ v_ini' = v_ini
       /\ pc' = "Check"
    \/ /\ pc = "Check"
       /\ u # v
       /\ pc' = "Start"
    \/ /\ pc = "Check"
       /\ u = v
       /\ pc' = "Done"

Spec ==
  Init /\ [][Next]_<<pc, u, v, v_ini>> /\ WF_[Next]_<<pc, u, v, v_ini>>

(* Fairness conditions *)
WF_spec == WF_[Next]_<<pc, u, v, v_ini>>

(* Termination property *)
Termination ==
  <>[](pc = "Done")

=============================================================================