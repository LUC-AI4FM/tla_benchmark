---------------- MODULE FairCounter ----------------

EXTENDS Integers

VARIABLES x, pc

vars == <<x, pc>>

Init ==
  /\ x = 0
  /\ pc = "Loop"

Increment ==
  /\ pc = "Loop"
  /\ x < 10
  /\ x' = x + 1
  /\ pc' = pc

GoToDone ==
  /\ pc = "Loop"
  /\ x >= 10
  /\ pc' = "Done"
  /\ x' = x

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ Increment
  \/ GoToDone
  \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

AtFive == x = 5

FinishLoop == x >= 10

PossibleCounts == x \in 0..10

=============================================================================