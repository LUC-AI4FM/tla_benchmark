```
MODULE RingSystem
EXTENDS Integers, FiniteSets
CONSTANTS N
VARIABLES pc, sharedReg, resultReg

Init ==
  /\ pc = [i \in 1..N |-> "start"]
  /\ sharedReg = [i \in 1..N |-> 0]
  /\ resultReg = [i \in 1..N |-> 0]

Next ==
  \/ \E i \in 1..N :
      pc[i] = "start"
      /\ pc' = [pc EXCEPT ![i] = "between"]
      /\ sharedReg' = [sharedReg EXCEPT ![i] = 1]
      /\ resultReg' = resultReg
      /\ UNCHANGED <<pc, sharedReg, resultReg>>[i]
  \/ \E i \in 1..N :
      pc[i] = "between"
      /\ pc' = [pc EXCEPT ![i] = "terminated"]
      /\ resultReg' = [resultReg EXCEPT ![i] = sharedReg[(i-1) % N + 1]]
      /\ sharedReg' = sharedReg
      /\ UNCHANGED <<pc, sharedReg, resultReg>>[i]
  \/ \E i \in 1..N :
      pc[i] = "terminated"
      /\ UNCHANGED <<pc, sharedReg, resultReg>>

Spec ==
  Init /\ [][Next]_<<pc, sharedReg, resultReg>>
  /\ WF_<<pc, sharedReg, resultReg>>(Next)

TypeInvariant ==
  /\ pc \in [1..N -> {"start", "between", "terminated"}]
  /\ sharedReg \in [1..N -> {0, 1}]
  /\ resultReg \in [1..N -> {0, 1}]

SafetyProperty ==
  []<>(\A i \in 1..N : pc[i] = "terminated") => \E i \in 1..N : resultReg[i] = 1

THEOREM Spec => []TypeInvariant
THEOREM Spec => SafetyProperty
THEOREM Spec => <>(\A i \in 1..N : pc[i] = "terminated")
```