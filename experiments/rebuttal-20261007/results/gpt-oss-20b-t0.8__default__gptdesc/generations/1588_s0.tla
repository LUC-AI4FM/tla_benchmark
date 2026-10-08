------------------------------ MODULE Euclid ------------------------------
EXTENDS Naturals

CONSTANT N

VARIABLES pc, u, v, v_ini

(* Initial condition: 24 and a chosen value from 1..N *)
Init == /\ u = 24
       /\ v \in 1 .. N
       /\ v_ini = v
       /\ pc = "Loop"

(* Transition when the two values are unequal *)
StepNonEqual ==
    /\ pc = "Loop"
    /\ u # v
    /\ u' = IF u > v THEN u - v ELSE u
    /\ v' = IF u > v THEN v ELSE v - u
    /\ pc' = "Loop"
    /\ UNCHANGED v_ini

(* Transition when the two values become equal *)
StepEqual ==
    /\ pc = "Loop"
    /\ u = v
    /\ pc' = "Done"
    /\ u' = u
    /\ v' = v
    /\ UNCHANGED v_ini

(* Stuttering step: identity transition *)
Stutter ==
    /\ pc' = pc
    /\ u' = u
    /\ v' = v
    /\ UNCHANGED v_ini

Next == StepNonEqual \/ StepEqual \/ Stutter

Spec == Init /\ [][Next]_<<pc, u, v, v_ini>> /\ WF_0(Next)

Termination == <> (pc = "Done")

=============================================================================