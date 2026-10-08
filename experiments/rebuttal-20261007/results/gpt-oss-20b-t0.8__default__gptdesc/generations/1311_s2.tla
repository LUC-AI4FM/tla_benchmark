MODULE GCD
EXTENDS Integers, Sequences

VARIABLES u, v, pc

vars == <<u, v, pc>>

Init ==
  /\ u = 24
  /\ v ∈ 1..50
  /\ pc = "loop"

SwapAction ==
  /\ pc = "loop"
  /\ u < v
  /\ u' = v
  /\ v' = u
  /\ pc' = "loop"

SubtractNonZeroAction ==
  /\ pc = "loop"
  /\ u >= v
  /\ u - v > 0
  /\ u' = u - v
  /\ v' = v
  /\ pc' = "loop"

SubtractZeroAction ==
  /\ pc = "loop"
  /\ u >= v
  /\ u - v = 0
  /\ u' = 0
  /\ v' = v
  /\ pc' = "done"

DoneStutter ==
  /\ pc = "done"
  /\ u' = u
  /\ v' = v
  /\ pc' = pc

Next == SwapAction \/ SubtractNonZeroAction \/ SubtractZeroAction \/ DoneStutter

Spec == Init /\ [][Next]_{vars}