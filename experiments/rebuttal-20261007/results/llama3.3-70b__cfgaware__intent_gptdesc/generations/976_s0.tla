---------------------------- MODULE RingSystem ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES pc, sharedReg, resultReg

pc == [i \in 1..N |-> "start"]
sharedReg == [i \in 1..N |-> 0]
resultReg == [i \in 1..N |-> 0]

Write(i) ==
  /\ pc[i] = "start"
  /\ sharedReg' = [sharedReg EXCEPT ![i] = 1]
  /\ resultReg' = resultReg
  /\ pc' = [pc EXCEPT ![i] = "between"]
  /\ UNCHANGED << >>

Read(i) ==
  /\ pc[i] = "between"
  /\ sharedReg' = sharedReg
  /\ resultReg' = [resultReg EXCEPT ![i] = sharedReg[(i-1 # N)]]
  /\ pc' = [pc EXCEPT ![i] = "terminated"]
  /\ UNCHANGED << >>

Next ==
  \/ \E i \in 1..N : Write(i)
  \/ \E i \in 1..N : Read(i)

Spec == Initialize /\ [][Next]_

TypeOK ==
  /\ pc \in [1..N -> {"start", "between", "terminated"}]
  /\ sharedReg \in [1..N -> {0, 1}]
  /\ resultReg \in [1..N -> {0, 1}]

Inv == TypeOK /\ (pc # "terminated" = {}) => \E i \in 1..N : resultReg[i] = 1

PCorrect == []<>(\A i \in 1..N : pc[i] = "terminated") => Inv
=============================================================================