MODULE GCDPlusCal

EXTENDS Naturals

VARIABLES u, v, pc

Init == /\ u = 24
        /\ pc = "Choose"

ChooseV ==
  /\ pc = "Choose"
  /\ v \in 1 .. 50
  /\ pc' = "Check"
  /\ u' = u
  /\ v' = v

CheckSwap ==
  /\ pc = "Check"
  /\ u < v
  /\ pc' = "Swap"
  /\ u' = u
  /\ v' = v

CheckSubtract ==
  /\ pc = "Check"
  /\ u >= v
  /\ pc' = "Subtract"
  /\ u' = u
  /\ v' = v

CheckDone ==
  /\ pc = "Check"
  /\ u = 0
  /\ pc' = "Done"
  /\ u' = u
  /\ v' = v

Subtract ==
  /\ pc = "Subtract"
  /\ u > 0
  /\ u' = u - v
  /\ pc' = "Check"
  /\ v' = v

Swap ==
  /\ pc = "Swap"
  /\ LET tmp == u IN
     /\ u' = v
     /\ v' = tmp
     /\ pc' = "Check"

StutterDone ==
  /\ pc = "Done"
  /\ pc' = pc
  /\ u' = u
  /\ v' = v

Next ==
  ChooseV \/ CheckSwap \/ CheckSubtract \/ CheckDone \/ Subtract \/ Swap \/ StutterDone

Spec == Init /\ [] (Next)

END MODULE