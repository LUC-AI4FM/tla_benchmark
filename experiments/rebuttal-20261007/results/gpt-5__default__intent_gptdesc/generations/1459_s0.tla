----------------------------- MODULE SaturatingCounter -----------------------------

EXTENDS Naturals

CONSTANTS SAT

VARIABLES c

ASSUME SAT = 3

Init ==
  c = 0

Incr ==
  /\ c < SAT
  /\ c' = c + 1

Stutter ==
  c' = c

Next ==
  Incr \/ Stutter

vars == << c >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Incr)

=============================================================================