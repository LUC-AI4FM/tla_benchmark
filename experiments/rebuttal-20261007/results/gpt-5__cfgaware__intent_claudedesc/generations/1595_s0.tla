----------------------------- MODULE FairCounter -----------------------------

EXTENDS Naturals

VARIABLE cnt

Init == cnt = 0

Inc ==
  /\ cnt < 10
  /\ cnt' = cnt + 1

Next == Inc

vars == << cnt >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Inc)

Termination == <>[](cnt = 10)

=============================================================================