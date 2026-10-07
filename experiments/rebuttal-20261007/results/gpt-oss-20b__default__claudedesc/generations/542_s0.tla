MODULE Increment
EXTENDS Naturals, TLC

CONSTANTS ProcA, ProcB

VARIABLES x, pc

Init == /\ x = 0
        /\ pc[ProcA] = "Start"
        /\ pc[ProcB] = "Start"

a ==
  /\ pc[ProcA] = "Start"
  /\ x' = x + 1
  /\ pc'[ProcA] = "Done"
  /\ pc'[ProcB] = pc[ProcB]

b ==
  /\ pc[ProcB] = "Start"
  /\ x' = x + 1
  /\ pc'[ProcB] = "Done"
  /\ pc'[ProcA] = pc[ProcA]

Terminate ==
  /\ pc[ProcA] = "Done" /\ pc[ProcB] = "Done"
  /\ UNCHANGED <<x, pc>>

Next == a \/ b \/ Terminate

Spec == Init /\ [][Next]_<<x, pc>>

TerminationProp == <> (pc[ProcA] = "Done" /\ pc[ProcB] = "Done")