------------------------------ MODULE GCD ------------------------------
EXTENDS Naturals

CONSTANTS UInit, VMin, VMax

VARIABLES u, v, pc

vars == <<u,v,pc>>

(* --- Initialization --------------------------------------------------- *)
Init ==
  /\ u = UInit
  /\ v \in VMin .. VMax
  /\ pc = 0

(* --- Step when checking whether a swap is needed ----------------------- *)
StepCheck ==
  /\ pc = 0
  /\ IF u < v THEN
       LET tmp == u IN
          /\ u' = v
          /\ v' = tmp
          /\ pc' = 1
     ELSE
        /\ u' = u
        /\ v' = v
        /\ pc' = 1

(* --- Subtraction step ------------------------------------------------- *)
StepSub ==
  /\ pc = 1
  /\ IF u > 0 THEN
       /\ u' = u - v
       /\ v' = v
       /\ pc' = 1
     ELSE
        /\ u' = u
        /\ v' = v
        /\ pc' = 2

(* --- Stuttering step in the terminating state ------------------------ *)
StepDone ==
  /\ pc = 2
  /\ u' = u
  /\ v' = v
  /\ pc' = 2

Next == StepCheck \/ StepSub \/ StepDone

Spec == Init /\ [][Next]_vars

=============================================================================