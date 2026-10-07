------------------------------ MODULE Outer ------------------------------
EXTENDS Naturals

VARIABLE outerX

I == INSTANCE Inner WITH x <- outerX

Init == outerX = 0

Next ==
  I!Inc
  \/ (~ENABLED I!Inc /\ UNCHANGED outerX)

Spec ==
  Init
  /\ [] (Next)
  /\ I!Fairness
  /\ <> (outerX = 3)
=============================================================================