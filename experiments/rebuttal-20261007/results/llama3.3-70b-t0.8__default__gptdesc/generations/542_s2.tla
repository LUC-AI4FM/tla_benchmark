```
MODULE SimplePlusCal
EXTENDS Integers

CONSTANTS ProcA, ProcB

VARIABLES x, pc

Init ==
  /\ x = 0
  /\ pc = [ProcA |-> "Start", ProcB |-> "Start"]

Next ==
  \/ ProcAIncrement
  \/ ProcBIncrement
  \/ Terminating

ProcAIncrement ==
  /\ pc[ProcA] = "Start"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !ProcA = "Done"]
  /\ UNCHANGED <<pc[ProcB], x>>

ProcBIncrement ==
  /\ pc[ProcB] = "Start"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !ProcB = "Done"]
  /\ UNCHANGED <<pc[ProcA], x>>

Terminating ==
  /\ pc[ProcA] = "Done"
  /\ pc[ProcB] = "Done"
  /\ UNCHANGED <<x, pc>>

Spec == Init /\ [][Next]_<<x, pc>>
Termination == <><ProcAIncrement \/ ProcBIncrement> 

THEOREM Spec => []<>Terminating
```