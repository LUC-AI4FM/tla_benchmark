```
MODULE SimpleConcurrentProgram
EXTENDS Integers

CONSTANTS ProcA, ProcB

VARIABLES x, pc

Init ==
  (x = 0) /\
  (pc = [ProcA |-> "Start", ProcB |-> "Start"])

Next ==
  \/ /\ pc[ProcA] = "Start"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT ![ProcA] = "Done"]
     /\ UNCHANGED pc[ProcB]
  \/ /\ pc[ProcB] = "Start"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT ![ProcB] = "Done"]
     /\ UNCHANGED pc[ProcA]
  \/ Terminating

Terminating ==
  /\ pc[ProcA] = "Done"
  /\ pc[ProcB] = "Done"
  /\ UNCHANGED x
  /\ UNCHANGED pc

Spec == Init /\ [][Next]_<<x, pc>>
Termination == <>[](pc[ProcA] = "Done" /\ pc[ProcB] = "Done")

THEOREM Spec => []Termination
```