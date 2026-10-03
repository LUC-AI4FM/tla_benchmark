------------------------------ MODULE Euclid ------------------------------
EXTENDS Naturals, Sequences, Temporal

CONSTANT N

VARIABLES pc, u, v, v_ini

(* --algorithm Euclid
variables u = 24, v, v_ini;
pc := "Start";
while (u != v) {
    if (u > v) { u := u - v; }
    else { v := v - u; }
}
pc := "Done";
--*)

Init ==
  /\ pc = "Start"
  /\ u = 24
  /\ v ∈ 1..N
  /\ v_ini = v

AlgorithmStep ==
  \/ /\ pc = "Start" /\ pc' = "Loop"
     /\ u' = u
     /\ v' = v
     /\ v_ini' = v_ini
  \/ /\ pc = "Loop" /\ u ≠ v /\ u > v
     /\ u' = u - v
     /\ v' = v
     /\ pc' = "Loop"
     /\ v_ini' = v_ini
  \/ /\ pc = "Loop" /\ u ≠ v /\ u < v
     /\ v' = v - u
     /\ u' = u
     /\ pc' = "Loop"
     /\ v_ini' = v_ini
  \/ /\ pc = "Loop" /\ u = v
     /\ pc' = "Done"
     /\ u' = u
     /\ v' = v
     /\ v_ini' = v_ini

Stutter ==
  /\ pc' = pc
  /\ u' = u
  /\ v' = v
  /\ v_ini' = v_ini

Next == AlgorithmStep \/ Stutter

vars == {pc, u, v, v_ini}

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

=============================================================================