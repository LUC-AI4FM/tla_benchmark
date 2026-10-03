---- MODULE Counter ----
EXTENDS Integers

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x = 0
  /\ pc = "Loop"

Tick ==
  /\ pc = "Loop"
  /\ x < 10
  /\ x' = x + 1
  /\ pc' = "Loop"

Exit ==
  /\ pc = "Loop"
  /\ x >= 10
  /\ x' = x
  /\ pc' = "Done"

Next == Tick \/ Exit

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

AtFive == x = 5

FinishLoop == /\ pc = "Done" /\ x = 10

PossibleCounts ==
  [ "Loop" |-> 0..10,
    "Done" |-> {10} ]

====