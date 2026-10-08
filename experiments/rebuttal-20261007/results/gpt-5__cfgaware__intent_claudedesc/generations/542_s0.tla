------------------------------ MODULE ConcurrentIncrement ------------------------------

EXTENDS Naturals

VARIABLES x, done1, done2

Init ==
  /\ x = 0
  /\ done1 = FALSE
  /\ done2 = FALSE

Inc1 ==
  /\ ~done1
  /\ x' = x + 1
  /\ done1' = TRUE
  /\ UNCHANGED done2

Inc2 ==
  /\ ~done2
  /\ x' = x + 1
  /\ done2' = TRUE
  /\ UNCHANGED done1

Next ==
  Inc1 \/ Inc2

vars == << x, done1, done2 >>

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Inc1) /\ WF_vars(Inc2)

==============================