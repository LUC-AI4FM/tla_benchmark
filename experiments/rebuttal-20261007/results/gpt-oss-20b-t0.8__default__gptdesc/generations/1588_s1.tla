MODULE Euclid
EXTENDS Naturals, Sequences

CONSTANT N \in Nat

VARIABLES pc, u, v, v_ini

vars == <<pc, u, v, v_ini>>

(* --- Initialization ----------------------------------------------------- *)
Init ==
  /\ pc = "Start"
  /\ u = 24
  /\ v ∈ 1..N
  /\ v_ini = v

(* --- Actions that change the state -------------------------------------- *)
SubtractU ==
  /\ pc ∈ {"Start","Loop"}
  /\ u > v
  /\ pc' = "Loop"
  /\ u' = u - v
  /\ v' = v

SubtractV ==
  /\ pc ∈ {"Start","Loop"}
  /\ v > u
  /\ pc' = "Loop"
  /\ u' = u
  /\ v' = v - u

DoneAction ==
  /\ (u = v)
  /\ pc' = "Done"
  /\ u' = u
  /\ v' = v

(* --- Stuttering step ----------------------------------------------------- *)
Stutter ==
  /\ pc' = pc
  /\ u' = u
  /\ v' = v

(* --- One complete step (may be a real transition or stuttering) --------- *)
Step == SubtractU \/ SubtractV \/ DoneAction \/ Stutter

(* --- The set of real transitions ---------------------------------------- *)
Next == SubtractU \/ SubtractV \/ DoneAction

(* --- Specification ------------------------------------------------------- *)
Spec ==
  Init
  /\ [][Step]_vars
  /\ WF_vars(Next)

(* --- Liveness property: eventually reach the "Done" state ----------------*)
Termination == <> (pc = "Done")

THEOREM EuclidTermination: Spec => Termination

===============================================================================