```
MODULE PlusCalAlgorithm
EXTENDS Integers

CONSTANTS ProcA, ProcB

VARIABLES pc, x

Init ==
  /\ pc = [ProcA |-> "Start", ProcB |-> "Start"]
  /\ x = 0

Next ==
  \/ (pc[ProcA] = "Start")
      /\ pc' = [pc EXCEPT ![ProcA] = "Inc"]
      /\ x' = x + 1
  \/ (pc[ProcB] = "Start")
      /\ pc' = [pc EXCEPT ![ProcB] = "Inc"]
      /\ x' = x + 1
  \/ (pc[ProcA] = "Inc")
      /\ pc' = [pc EXCEPT ![ProcA] = "Done"]
      /\ x' = x
  \/ (pc[ProcB] = "Inc")
      /\ pc' = [pc EXCEPT ![ProcB] = "Done"]
      /\ x' = x
  \/ (pc[ProcA] = "Done") /\ (pc[ProcB] = "Done")
      /\ pc' = pc
      /\ x' = x

Spec == Init /\ [][Next]_<<pc, x>>
Termination == <>(pc[ProcA] = "Done" /\ pc[ProcB] = "Done")

THEOREM Spec => []Termination
```