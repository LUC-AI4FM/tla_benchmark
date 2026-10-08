---- MODULE CounterInner ----
EXTENDS Naturals

CONSTANT N
VARIABLE x

Init ==
  x = 0

Inc ==
  /\ x < N
  /\ x' = x + 1

Next ==
  Inc \/ UNCHANGED x

Spec ==
  /\ Init
  /\ [][Next]_x
  /\ WF_x(Inc)

WFair ==
  WF_x(Inc)

TypeOK ==
  x \in 0..N

Termination ==
  <> (x = N)
====