------------------------------ MODULE RandomTest ------------------------------
EXTENDS Randomization

CONSTANTS S, T

VARIABLE x

Init ==
  /\ x = RandomSubset([S -> T], 1000)

Next ==
  /\ x' = x

Spec == Init /\ [][Next]_<<x>>

=============================================================================