---- MODULE Outer ----
EXTENDS Sequences

VARIABLES res, seq

vars == <<res, seq>>

I == INSTANCE Inner WITH Res <- res, S <- seq

Init ==
  /\ res = 0
  /\ seq = <<0, 1, 2, 1>>

StutterWhenDisabled ==
  /\ ~ENABLED I!Step
  /\ UNCHANGED vars

Next ==
  I!Step \/ StutterWhenDisabled

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(I!Step)

SpecRunsToEnd ==
  <>[] (~ENABLED I!Step)

====