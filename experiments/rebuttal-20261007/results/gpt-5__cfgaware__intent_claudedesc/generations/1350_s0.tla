------------------------------ MODULE CounterWF ------------------------------

EXTENDS Naturals

VARIABLE c

Init ==
  c = 1

Inc ==
  c < 5 /\ c' = c + 1

Next ==
  Inc

Spec ==
  Init /\ [][Next]_c /\ WF_c(Inc)

Liveness ==
  <>[] (c = 5)

============================================================================