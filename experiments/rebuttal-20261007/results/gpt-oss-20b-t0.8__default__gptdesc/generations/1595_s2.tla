MODULE Counter
EXTENDS Naturals

VARIABLES x, pc

maxCount == 10

Init ==
  /\ x = 0
  /\ pc = "Inc"

Next ==
  \/ /\ pc = "Inc" /\ x < maxCount
      /\ x' = x + 1
      /\ pc' = "Inc"
  \/ /\ pc = "Inc" /\ x >= maxCount
      /\ pc' = "Done"
      /\ x' = x

Spec == Init /\ [][Next]_<<x,pc>> /\ WF(Next) /\ <> (pc = "Done")

AtFive ==
  x = 5

FinishLoop ==
  pc = "Done"

PossibleCounts ==
  /\ x \in 0..maxCount

CHECK PossibleCounts

===============================================================================