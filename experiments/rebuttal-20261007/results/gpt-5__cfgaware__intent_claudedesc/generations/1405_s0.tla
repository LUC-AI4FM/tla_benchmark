----------------------------- MODULE OuterInstantiatesInner -----------------------------
EXTENDS Naturals, Sequences

VARIABLES res, seq

I == INSTANCE InnerModel WITH x <- res, s <- seq

Init ==
  /\ res = 0
  /\ seq = <<1, 2, 3>>

CanInner == Enabled I!Step

Next ==
  \/ I!Step
  \/ /\ ~CanInner
     /\ UNCHANGED <<res, seq>>

Spec ==
  Init /\ [][Next]_<<res, seq>> /\ WF_<<res, seq>>(I!Step)

SpecRunsToEnd ==
  <>[] ~Enabled I!Step
=============================================================================