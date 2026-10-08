MODULE Euclid
EXTENDS Naturals, Integers

CONSTANTS MaxNum, MaxSteps

VARIABLES u_ini, v_ini, u, v, pc, stepCnt

PcStates == {"Init", "SetVars", "CheckCond", "Compute", "Done"}

Gcd(x, y) ==
  IF y = 0 THEN x
  ELSE Gcd(y, x % y)

(* ----------------------------------------------------------------- *)
(* Initial state *)
Init ==
  /\ pc = "Init"
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u \in 0..MaxNum
  /\ v \in 0..MaxNum
  /\ stepCnt = 0

(* ----------------------------------------------------------------- *)
(* Actions *)

InitToSet ==
  /\ pc = "Init"
  /\ pc' = "SetVars"
  /\ UNCHANGED <<u_ini, v_ini, u, v, stepCnt>>

SetVars ==
  /\ pc = "SetVars"
  /\ u' = u_ini
  /\ v' = v_ini
  /\ pc' = "CheckCond"
  /\ UNCHANGED <<stepCnt>>

CheckCondZero ==
  /\ pc = "CheckCond"
  /\ v = 0
  /\ pc' = "Done"
  /\ UNCHANGED <<u, u_ini, v_ini, stepCnt>>

CheckCondNonzero ==
  /\ pc = "CheckCond"
  /\ v # 0
  /\ pc' = "Compute"
  /\ UNCHANGED <<u, u_ini, v_ini, stepCnt>>

Compute ==
  LET temp == u % v IN
    /\ pc = "Compute"
    /\ u' = v
    /\ v' = temp
    /\ pc' = "CheckCond"
    /\ stepCnt' = stepCnt + 1
    /\ UNCHANGED <<u_ini, v_ini>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED <<u_ini, v_ini, u, v, stepCnt>>

Next ==
  \/ InitToSet
  \/ SetVars
  \/ CheckCondZero
  \/ CheckCondNonzero
  \/ Compute
  \/ Done

(* ----------------------------------------------------------------- *)
(* Invariants *)

NoNegativeStep == stepCnt >= 0

WithinBounds ==
  /\ u \in 0..MaxNum
  /\ v \in 0..MaxNum

PcInvariants == pc \in PcStates

Correctness == (pc = "Done") => (u = Gcd(u_ini, v_ini))

StepBound == stepCnt <= MaxSteps

AllInvariants ==
  NoNegativeStep /\ WithinBounds /\ PcInvariants /\ Correctness /\ StepBound

(* ----------------------------------------------------------------- *)
(* Specification *)

Spec == Init
        /\ [][Next]_<<u_ini, v_ini, u, v, pc, stepCnt>>
        /\ WF_acts(Next)

============================================================

(* TLC counting expectation example *)
CONSTANTS MaxNum, MaxSteps