---------------------------- MODULE SimpleConcurrentAlgorithm ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLES pc, sharedArray1, sharedArray2

TypeOK == 
  /\ pc \in [0..N-1 -> {"step1", "step2", "done"}]
  /\ sharedArray1 \in [0..N-1 -> {0, 1}]
  /\ sharedArray2 \in [0..N-1 -> {0, 1}]

Inv == 
  /\ TypeOK
  /\ (pc = <<>>) => (* Initial condition: all processes are at step1 *)
    /\ sharedArray1 = [i \in 0..N-1 |-> 0]
    /\ sharedArray2 = [i \in 0..N-1 |-> 0]
  /\ (pc = [i \in 0..N-1 |-> "done"]) => (* All processes have finished *)
    (\E i \in 0..N-1 : sharedArray2[i] = 1)

Spec == 
  /\ TypeOK
  /\ [][
      \/ \E i \in 0..N-1 :
        /\ pc[i] = "step1"
        /\ pc' = [pc EXCEPT ![i] = "step2"]
        /\ sharedArray1' = [sharedArray1 EXCEPT ![i] = 1]
        /\ sharedArray2' = sharedArray2
      \/ \E i \in 0..N-1 :
        /\ pc[i] = "step2"
        /\ pc' = [pc EXCEPT ![i] = "done"]
        /\ sharedArray1' = sharedArray1
        /\ sharedArray2' = [sharedArray2 EXCEPT ![i] = sharedArray1[(i-1) % N]]
      \/ (* stuttering step *)
        pc' = pc
        /\ sharedArray1' = sharedArray1
        /\ sharedArray2' = sharedArray2
    ]

PCorrect == 
  <><Inv /\ [][Spec]>>_pc,sharedArray1,sharedArray2

THEOREM Spec => []Inv
PROOF * Omitted for brevity *

=============================================================================