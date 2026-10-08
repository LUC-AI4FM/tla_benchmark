```
MODULE SimplePlusCal
EXTENDS Integers

CONSTANTS ProcA, ProcB

VARIABLES x, pcA, pcB

Init ==
  /\ x = 0
  /\ pcA = "Start"
  /\ pcB = "Start"

Next ==
  \/ (pcA = "Start") /\ (pcA' = "Done") /\ (x' = x + 1) /\ (pcB' = pcB)
  \/ (pcB = "Start") /\ (pcB' = "Done") /\ (x' = x + 1) /\ (pcA' = pcA)
  \/ (pcA = "Done") /\ (pcB = "Done") /\ (x' = x) /\ (pcA' = pcA) /\ (pcB' = pcB)

Spec ==
  Init /\ [][Next]_<<x, pcA, pcB>>

Terminating ==
  (pcA = "Done") /\ (pcB = "Done")

THEOREM Spec => []<>(Terminating)
```