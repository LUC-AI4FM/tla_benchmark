------------------------------ MODULE GCDSubtraction ------------------------------
EXTENDS Naturals

VARIABLES u, v, pc

(* State constants *)
ChooseVState == 0
LoopStartState == 1
SwapState == 2
SubtractState == 3
DoneState == 4

Init ==
  /\ u = 24
  /\ v = 0
  /\ pc = ChooseVState

ChooseVStep ==
  /\ pc = ChooseVState
  /\ v' \in 1 .. 50
  /\ pc' = LoopStartState
  /\ u' = u

LoopStartStep ==
  /\ pc = LoopStartState
  /\ IF u < v THEN pc' = SwapState ELSE pc' = SubtractState
  /\ u' = u
  /\ v' = v

SwapStep ==
  /\ pc = SwapState
  /\ u' = v
  /\ v' = u
  /\ pc' = LoopStartState

SubtractStep ==
  /\ pc = SubtractState
  /\ u' = u - v
  /\ IF u' = 0 THEN pc' = DoneState ELSE pc' = SubtractState
  /\ v' = v

DoneStutter ==
  /\ pc = DoneState
  /\ pc' = DoneState
  /\ u' = u
  /\ v' = v

Next == 
  \/ ChooseVStep
  \/ LoopStartStep
  \/ SwapStep
  \/ SubtractStep
  \/ DoneStutter

Safety ==
  /\ u \in Nat
  /\ v \in Nat
  /\ (pc = DoneState => u = 0)
  /\ (pc = SubtractState => u >= v)

Spec == Init /\ [][Next]_vars /\ [](Safety)

=============================================================================