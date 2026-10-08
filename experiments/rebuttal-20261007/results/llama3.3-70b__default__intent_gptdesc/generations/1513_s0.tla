```
MODULE TokenPassingTerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS ProcSet, ColorSet
ASSUME ProcSet = {1, 2, 3}
ASSUME ColorSet = {0, 1}

VARIABLES tokenProc, tokenColor, procActivity, procColor, workPending

Init ==
  /\ tokenProc \in ProcSet
  /\ tokenColor \in ColorSet
  /\ procActivity \in [ProcSet -> {0, 1}]
  /\ procColor \in [ProcSet -> ColorSet]
  /\ workPending \in [ProcSet -> {0, 1}]

Next ==
  \/ \E p \in ProcSet :
    /\ tokenProc = p
    /\ procActivity' = [procActivity EXCEPT ![p] = 1]
    /\ procColor' = [procColor EXCEPT ![p] = IF tokenColor = 0 THEN 1 ELSE 0]
    /\ workPending' = [workPending EXCEPT ![p] = 1]
    /\ tokenProc' = IF p = 3 THEN 1 ELSE (p + 1)
    /\ tokenColor' = tokenColor
  \/ \E p \in ProcSet :
    /\ tokenProc = p
    /\ procActivity' = [procActivity EXCEPT ![p] = 0]
    /\ procColor' = procColor
    /\ workPending' = [workPending EXCEPT ![p] = 0]
    /\ tokenProc' = IF p = 3 THEN 1 ELSE (p + 1)
    /\ tokenColor' = IF \A q \in ProcSet : procActivity[q] = 0 /\ workPending[q] = 0 THEN 1 ELSE tokenColor
  \/ \E p \in ProcSet :
    /\ tokenProc = p
    /\ procActivity' = procActivity
    /\ procColor' = procColor
    /\ workPending' = workPending
    /\ tokenProc' = IF p = 3 THEN 1 ELSE (p + 1)
    /\ tokenColor' = tokenColor

Spec ==
  Init /\ [][Next]_<<tokenProc, tokenColor, procActivity, procColor, workPending>>

TerminationDetector ==
  <>(\A p \in ProcSet : procActivity[p] = 0 /\ workPending[p] = 0) /\ tokenColor = 1

THEOREM Spec => []<>(TerminationDetector)
THEOREM Spec => [](~TerminationDetector => <>(~TerminationDetector))

WF_Vars == <<tokenProc, tokenColor, procActivity, procColor, workPending>>
Fairness ==
  /\ [][Next]_WF_Vars
  /\ WF_Vars(tokenProc')
  /\ WF_Vars(procActivity')
  /\ WF_Vars(workPending')

INV_Safety1 == tokenProc \in ProcSet
INV_Safety2 == tokenColor \in ColorSet
INV_Safety3 == \A p \in ProcSet : procActivity[p] \in {0, 1}
INV_Safety4 == \A p \in ProcSet : procColor[p] \in ColorSet

THEOREM Spec => []INV_Safety1
THEOREM Spec => []INV_Safety2
THEOREM Spec => []INV_Safety3
THEOREM Spec => []INV_Safety4
```