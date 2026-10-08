------------------------------ MODULE CounterInner ------------------------------
EXTENDS Naturals

VARIABLE x

StepInner == /\ x < 3
          /\ x' = x + 1

END MODULE

--------------------------------- MODULE CounterOuter ---------------------------------
EXTENDS Naturals, TLC

VARIABLE outerX

INSTANCE CounterInner WITH x = outerX

Init ==
  /\ outerX = 0

Next ==
  \/ (outerX < 3 /\ outerX' = outerX + 1)
  \/ (~(outerX < 3) /\ outerX' = outerX)

Spec == Init
       /\ [][Next]_outerX
       /\ WF_Exists(StepInner)

LivenessProp == <> (outerX = 3)

END MODULE