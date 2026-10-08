----------------------------- MODULE GCDLoop -----------------------------

EXTENDS Integers

CONSTANTS v_range

VARIABLES pc, u, v

Init == 
  /\ pc = "Start"
  /\ u = 24
  /\ v \in 1..v_range

Next ==
  \/ /\ pc = "Start"
     /\ u = 24
     /\ v \in 1..v_range
     /\ UNCHANGED <<u, v>>
     /\ pc' = "Loop"

  \/ /\ pc = "Loop"
     /\ IF u < v THEN
          /\ u' = v
          /\ v' = u
          /\ pc' = "Loop"
        ELSE 
          /\ u' = u - v
          /\ v' = v
          /\ pc' = "Check"

  \/ /\ pc = "Check"
     /\ IF u = 0 THEN
          /\ pc' = "Done"
        ELSE
          /\ pc' = "Loop"

  \/ /\ pc = "Done"
     /\ UNCHANGED <<u, v>>
     /\ pc' = "Done"

Spec ==
  /\ Init
  /\ [][Next]_<<pc, u, v>>

=============================================================================