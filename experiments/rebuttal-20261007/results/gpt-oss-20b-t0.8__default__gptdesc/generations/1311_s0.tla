MODULE GCD
EXTENDS Naturals

VARIABLES u, v, pc

Init == 
  /\ u = 24
  /\ v \in 1..50
  /\ pc = "CheckSwap"

SwapStep ==
  /\ pc = "CheckSwap"
  /\ u > 0
  /\ u < v
  /\ u' = v
  /\ v' = u
  /\ pc' = "CheckSwap"

SubtractStep ==
  /\ pc = "CheckSwap"
  /\ u > 0
  /\ u >= v
  /\ u' = u - v
  /\ v' = v
  /\ pc' = "CheckSwap"

TerminateStep ==
  /\ pc = "CheckSwap"
  /\ u = 0
  /\ pc' = "Done"
  /\ u' = u
  /\ v' = v

StutterInDone ==
  /\ pc = "Done"
  /\ pc' = pc
  /\ u' = u
  /\ v' = v

Next == SwapStep \/ SubtractStep \/ TerminateStep \/ StutterInDone

Spec == Init /\ [] [Next]_<<u,v,pc>>