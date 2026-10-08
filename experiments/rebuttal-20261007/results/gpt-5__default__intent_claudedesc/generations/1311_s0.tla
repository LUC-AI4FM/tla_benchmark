------------------------------ MODULE EuclidGCD ------------------------------

EXTENDS Naturals

CONSTANT BOUND
ASSUME BOUND = 50

VARIABLES x, y

Init ==
  /\ x = 24
  /\ y \in 1..BOUND

Done == x = 0

StepGE ==
  /\ x > 0
  /\ x >= y
  /\ x' = x - y
  /\ y' = y

StepLT ==
  /\ x > 0
  /\ x < y
  /\ x' = y - x
  /\ y' = x

Next ==
  \/ Done /\ UNCHANGED <<x, y>>
  \/ StepGE
  \/ StepLT

Spec ==
  /\ Init
  /\ [][Next]_<<x, y>>
  /\ SF_<<x, y>>(StepGE \/ StepLT)

Termination ==
  <>Done

=============================================================================