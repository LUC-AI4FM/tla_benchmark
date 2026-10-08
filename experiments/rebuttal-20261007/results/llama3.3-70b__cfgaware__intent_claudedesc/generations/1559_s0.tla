--------------------------- MODULE AugmentedLock ---------------------------
EXTENDS Integers, TLC

CONSTANT ProcSet, Turn
VARIABLE pc, history, stutter, turn

TypeOKHS == 
  /\ pc \in [ProcSet -> {"entry", "critical", "exit"}]
  /\ history \in [ProcSet -> {0, 1}]
  /\ stutter \in [ProcSet -> {"step1", "step2", "step3"}]
  /\ turn \in {0, 1}

InvHS == 
  /\ TypeOKHS
  /\ (pc[1] = "critical") => (turn = 0)
  /\ (pc[2] = "critical") => (turn = 1)
  /\ (pc[1] = "entry") => (history[1] = turn)
  /\ (pc[2] = "entry") => (history[2] = turn)

LockInv == 
  /\ (pc[1] = "critical") => (turn = 0)
  /\ (pc[2] = "critical") => (turn = 1)

SpecHS ==
  /\ InitHS
  /\ [][NextHS]_<<pc, history, stutter, turn>>

InitHS == 
  /\ pc = [i \in ProcSet |-> "entry"]
  /\ history = [i \in ProcSet |-> 0]
  /\ stutter = [i \in ProcSet |-> "step1"]
  /\ turn = 0

NextHS ==
  /\ (pc[1] = "entry") 
    => (pc' = [pc EXCEPT ![1] = "critical"])
       /\ (stutter[1] = "step1") 
         => (stutter' = [stutter EXCEPT ![1] = "step2"])
         /\ (history' = [history EXCEPT ![1] = turn])
       /\ (stutter[1] = "step2") 
         => (stutter' = [stutter EXCEPT ![1] = "step3"])
       /\ (stutter[1] = "step3") 
         => (turn' = 1 - turn)
  /\ (pc[2] = "entry") 
    => (pc' = [pc EXCEPT ![2] = "critical"])
       /\ (stutter[2] = "step1") 
         => (stutter' = [stutter EXCEPT ![2] = "step2"])
         /\ (history' = [history EXCEPT ![2] = turn])
       /\ (stutter[2] = "step2") 
         => (stutter' = [stutter EXCEPT ![2] = "step3"])
       /\ (stutter[2] = "step3") 
         => (turn' = 1 - turn)
  /\ (pc[1] = "critical") 
    => (pc' = [pc EXCEPT ![1] = "exit"])
  /\ (pc[2] = "critical") 
    => (pc' = [pc EXCEPT ![2] = "exit"])
  /\ (pc[1] = "exit") 
    => (pc' = [pc EXCEPT ![1] = "entry"])
       /\ (stutter' = [stutter EXCEPT ![1] = "step1"])
  /\ (pc[2] = "exit") 
    => (pc' = [pc EXCEPT ![2] = "entry"])
       /\ (stutter' = [stutter EXCEPT ![2] = "step1"])
  /\ UNCHANGED <<history, turn>>

Spec == 
  /\ InitHS
  /\ [][NextHS]_<<pc, history, stutter, turn>>
  /\ InvHS

PSpec == 
  /\ InitHS
  /\ [][NextHS]_<<pc, history, stutter, turn>>
  /\ LockInv
=============================================================================