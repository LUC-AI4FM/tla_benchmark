----------------------------- MODULE TwoWorkerCounter -----------------------------

EXTENDS Naturals

VARIABLES cnt, done1, done2

vars == << cnt, done1, done2 >>

Init ==
  /\ cnt = 0
  /\ done1 = FALSE
  /\ done2 = FALSE

W1 ==
  /\ ~done1
  /\ done1' = TRUE
  /\ done2' = done2
  /\ cnt' = cnt + 1

W2 ==
  /\ ~done2
  /\ done2' = TRUE
  /\ done1' = done1
  /\ cnt' = cnt + 1

Next == W1 \/ W2

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(W1)
  /\ WF_vars(W2)

==============================================================================