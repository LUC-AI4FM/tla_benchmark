```tla
MODULE ProcIncrement

EXTENDS Integers, TLC

CONSTANTS ProcA, ProcB

VARIABLES x, pc

Init == 
  /\ x = 0
  /\ pc[ProcA] = "Start"
  /\ pc[ProcB] = "Start"

Next ==
  \/ /\ pc[ProcA] = "Start"
     /\ pc[ProcB] = _
     /\ x' = x + 1
     /\ pc'[ProcA] = "Done"
     /\ pc'[ProcB] = pc[ProcB]
  \/ /\ pc[ProcA] = _
     /\ pc[ProcB] = "Start"
     /\ x' = x + 1
     /\ pc'[ProcA] = pc[ProcA]
     /\ pc'[ProcB] = "Done"
  \/ Terminating

Terminating ==
  /\ pc[ProcA] = "Done"
  /\ pc[ProcB] = "Done"
  /\ UNCHANGED <<x, pc>>

Spec ==
  Init /\ [][Next]_<<x, pc>> /\ WF_[Next]_<<x, pc>>

Invariant1 == x \in {0, 1, 2}

Invariant2 ==
  \/ pc[ProcA] = "Start"
  \/ pc[ProcB] = "Start"
  \/ (pc[ProcA] = "Done" /\ pc[ProcB] = "Done")

Termination ==
  <>[](pc[ProcA] = "Done" /\ pc[ProcB] = "Done")
```