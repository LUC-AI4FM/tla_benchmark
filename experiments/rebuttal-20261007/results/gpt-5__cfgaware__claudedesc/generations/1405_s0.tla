----------------------------- MODULE Outer725f -----------------------------
EXTENDS Sequences

VARIABLES outerRes, outerSeq

Svc == INSTANCE Inner725f WITH res <- outerRes, myseq <- outerSeq

Init ==
  /\ outerRes = 0
  /\ outerSeq = <<1, 2, 3>>

Step ==
  Svc!Step \/ UNCHANGED <<outerRes, outerSeq>>

Spec ==
  Init /\ [][Step]_<<outerRes, outerSeq>> /\ Svc!Fairness

SpecRunsToEnd ==
  Spec => <>[] ~ENABLED Svc!Step
=============================================================================