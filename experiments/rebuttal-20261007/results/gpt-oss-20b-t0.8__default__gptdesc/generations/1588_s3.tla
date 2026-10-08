MODULE Euclid

EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES pc, u, v, v_ini

Init ==
  /\ pc = "Start"
  /\ u = 24
  /\ v_ini \in 1..N
  /\ v = v_ini

Next ==
  \/ /\ pc = "Start"
     /\ v_ini \in 1..N
     /\ u' = 24
     /\ v' = v_ini
     /\ pc' = "Subtraction"

  \/ /\ pc = "Subtraction" /\ u > v
     /\ u' = u - v
     /\ v' = v
     /\ pc' = "Subtraction"

  \/ /\ pc = "Subtraction" /\ v > u
     /\ v' = v - u
     /\ u' = u
     /\ pc' = "Subtraction"

  \/ /\ pc = "Subtraction" /\ u = v
     /\ u' = u
     /\ v' = v
     /\ pc' = "Done"

  \/ /\ pc' = pc
     /\ u' = u
     /\ v' = v
     /\ v_ini' = v_ini

Invariant ==
  /\ u >= 1
  /\ v >= 1

Spec == Init /\ [][Next]_<<pc,u,v, v_ini>> /\ WF/Next

Termination == <> (pc = "Done")

END MODULE