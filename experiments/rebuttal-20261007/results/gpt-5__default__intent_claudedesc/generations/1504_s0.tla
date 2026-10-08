------------------------------ MODULE Stationary ------------------------------

EXTENDS TLC

CONSTANTS D

VARIABLES b

Init ==
  b = TRUE

Next ==
  UNCHANGED b

Spec ==
  Init /\ [][Next]_b

AlwaysEnabled ==
  ENABLED Next

SafetyInvariant ==
  AlwaysEnabled

===============================================================================