---- MODULE Euclid ----
EXTENDS Naturals, Integers

CONSTANT MaxNum

VARIABLES pc, u_ini, v_ini, u, v, step

RECURSIVE GCD(a,b)
GCD(a,b) ==
  IF a = 0 THEN b
  ELSE IF b = 0 THEN a
  ELSE GCD(b, a MOD b)

Init == 
  /\ pc = "Start"
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u = u_ini
  /\ v = v_ini
  /\ step = 0

Next ==
  \/ (* Start to Loop *)
     /\ pc = "Start"
     /\ pc' = "Loop"

  \/ (* Subtraction step when u != v *)
     /\ pc = "Loop"
     /\ u # v
     /\ IF u > v THEN 
          /\ u' = u - v
          /\ v' = v
        ELSE 
          /\ u' = u
          /\ v' = v - u
     /\ pc' = "Loop"
     /\ step' = step + 1

  \/ (* Finish when u == v *)
     /\ pc = "Loop"
     /\ u = v
     /\ pc' = "Done"
     /\ u' = u
     /\ v' = v
     /\ step' = step

Spec ==
  Init /\ [][Next]_<<pc,u_ini,v_ini,u,v,step>> /\ WF_vars(Next) /\ Correctness

SafetyInv == 
  /\ pc \in {"Start", "Loop", "Done"}
  /\ u \in 1..MaxNum
  /\ v \in 1..MaxNum
  /\ step >= 0

Correctness ==
  (pc = "Done") => (u = GCD(u_ini, v_ini))

Termination == <> (pc = "Done")

StepBound == step <= MaxNum

=============================================================================