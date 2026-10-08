---------------------------- MODULE SharedMemoryAlgorithm ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES pc, sharedReg, localReg

Spec == 
  /\ pc = [i \in 1..N |-> "start"]
  /\ sharedReg = [i \in 1..N |-> 0]
  /\ localReg = [i \in 1..N |-> 0]
  /\ [][
      /\ \A i \in 1..N : 
        IF pc[i] = "start" THEN
          /\ sharedReg' = [sharedReg EXCEPT ![i] = 1]
          /\ localReg' = localReg
          /\ pc' = [pc EXCEPT ![i] = "writing"]
        ELSE IF pc[i] = "writing" THEN
          /\ sharedReg' = [sharedReg EXCEPT ![i] = 1]
          /\ localReg' = localReg
          /\ pc' = [pc EXCEPT ![i] = "written"]
        ELSE IF pc[i] = "written" THEN
          /\ sharedReg' = sharedReg
          /\ localReg' = [localReg EXCEPT ![i] = IF sharedReg[(i-1) % N + 1] = 0 THEN 0 ELSE 1]
          /\ pc' = [pc EXCEPT ![i] = "done"]
        ELSE
          /\ UNCHANGED <<sharedReg, localReg, pc>>
      /\ TypeOK'
  ]

TypeOK == 
  /\ pc \in [1..N -> {"start", "writing", "written", "done"}]
  /\ sharedReg \in [1..N -> {0, 1}]
  /\ localReg \in [1..N -> {0, 1}]

Inv == 
  /\ TypeOK
  /\ \A i \in 1..N : pc[i] = "start" OR pc[i] = "writing" OR pc[i] = "written" OR pc[i] = "done"
  /\ \E i \in 1..N : localReg[i] = 1

PCorrect == 
  <>[\A i \in 1..N : pc[i] = "done"]_<<pc, sharedReg, localReg>>
=============================================================================