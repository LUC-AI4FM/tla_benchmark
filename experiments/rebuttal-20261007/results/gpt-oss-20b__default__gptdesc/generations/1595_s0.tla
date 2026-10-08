MODULE FairCounter
EXTENDS Naturals

CONSTANTS

VARIABLES x, pc

Init ==
  /\ x = 0
  /\ pc = "Loop"

Next ==
  /\ pc = "Loop"
  /\ IF x < 10 THEN
        /\ x' = x + 1
        /\ pc' = "Loop"
     ELSE
        /\ pc' = "Done"
        /\ x' = x

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

AtFive == (x = 5)
FinishLoop == (pc = "Done")

PossibleCounts ==
  /\ x \in 0..10
  /\ pc \in {"Loop", "Done"}

THEOREM Termination == Spec => <> (pc = "Done")